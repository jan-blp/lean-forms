module

public import Forms.Model.FreshId
public import Forms.Model.Format
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Nodup

/-! Collections separate uuid from content. -/

@[expose] public section
namespace Forms.Model
open Lean

structure Item (β : Type) where
  id : Uuid
  value : β
  deriving BEq, DecidableEq, Repr, Lean.ToJson, Lean.FromJson

def Item.mapValue {β γ : Type} (f : β → γ) (item : Item β) : Item γ where
  id := item.id
  value := f item.value

theorem Item.id_mapValue
  {β γ : Type}
  (f : β → γ)
  (item : Item β)
  : (item.mapValue f).id = item.id :=
  rfl

/-- With `idKey := "uuid"`, decodes `{ "uuid": "...", "amount": 58 }` as
`{ id := ..., value := { amount := 58 } }`. The remaining fields are decoded as `β`. -/
def Item.flatFromJson?
  {β : Type}
  [FromJson β]
  (idKey : String)
  (json : Json)
  : Except String (Item β) := do
  let id ← fromJson? (← json.getObjVal? idKey)
  let value ← fromJson? (.obj ((← json.getObj?).erase idKey))
  pure { id, value }

/-- Writes an entry as a flat object with its id under `idKey`. -/
def Item.flatToJson? {β : Type} [ToJson β] (idKey : String) (item : Item β) : Except String Json :=
  match toJson item.value with
  | .obj fields =>
    if fields.contains idKey then .error s!"The content already has a field {idKey}."
    else .ok (.obj (fields.insert idKey (toJson item.id)))
  | .null
  | .bool _
  | .num _
  | .str _
  | .arr _ => .error "Only objects can hold an id field."

@[ext] structure Collection (β : Type) where
  entries : List (Item β)
  nodup : (entries.map Item.id).Nodup := by decide
  deriving DecidableEq

namespace Collection

variable {β γ : Type}

def empty : Collection β where
  entries := []
  nodup := List.nodup_nil

def ids (collection : Collection β) : List Uuid :=
  collection.entries.map Item.id

def values (collection : Collection β) : List β :=
  collection.entries.map Item.value

def length (collection : Collection β) : Nat :=
  collection.entries.length

def mapEntries
  (f : Item β → Item γ)
  (keeps : ∀ item, (f item).id = item.id)
  (collection : Collection β)
  : Collection γ where
  entries := collection.entries.map f
  nodup := by simpa [Function.comp_def, keeps] using collection.nodup

def map (f : β → γ) (collection : Collection β) : Collection γ :=
  collection.mapEntries (Item.mapValue f) (Item.id_mapValue f)

def mapWithId (f : Uuid → β → γ) (collection : Collection β) : Collection γ :=
  collection.mapEntries (fun item => { id := item.id, value := f item.id item.value }) fun _ => rfl

theorem ids_modify
  (entries : List (Item β))
  (index : Nat)
  (f : β → β)
  : (entries.modify index (Item.mapValue f)).map Item.id = entries.map Item.id := by
  induction entries generalizing index <;> cases index <;> simp_all [Item.mapValue]

def modifyAt (index : Nat) (f : β → β) (collection : Collection β) : Collection β where
  entries := collection.entries.modify index (Item.mapValue f)
  nodup := by simpa [ids_modify] using collection.nodup

theorem ids_modifyAt
  (index : Nat)
  (f : β → β)
  (collection : Collection β)
  : (collection.modifyAt index f).ids = collection.ids :=
  ids_modify collection.entries index f

def eraseAt (index : Nat) (collection : Collection β) : Collection β where
  entries := collection.entries.eraseIdx index
  nodup := collection.nodup.sublist ((List.eraseIdx_sublist _ _).map _)

def append
  (id : Uuid)
  (value : β)
  (collection : Collection β)
  (fresh : id ∉ collection.ids)
  : Collection β where
  entries := collection.entries ++ [{ id, value }]
  nodup := by simpa [List.nodup_append, ids, collection.nodup] using fresh

/-- Example data with the ids `Uuid.ofNat 1`, `Uuid.ofNat 2`, … -/
def numbered
  (values : List β)
  (fits : values.length ≤ 2^48 := by decide)
  : Collection β where
  entries := values.mapIdx fun index value => { id := .ofNat index.succ, value }
  nodup := by
    have distinct : ((List.range values.length).map (Uuid.ofNat ·.succ)).Nodup :=
      List.nodup_range.map_on fun first first_mem second second_mem same => by
        have first_bound := List.mem_range.mp first_mem
        have second_bound := List.mem_range.mp second_mem
        have equal := Uuid.ofNat_inj (by omega) (by omega) (by omega) (by omega) same
        omega
    convert distinct using 1
    apply List.ext_getElem <;> simp

structure IdCollision where
  id : Uuid
  deriving DecidableEq, Repr

def appendFresh
  {m : Type → Type}
  [Monad m]
  [MonadFreshId m]
  (value : β)
  (collection : Collection β)
  : ExceptT IdCollision m (Collection β) := do
  let id ← (freshId : m Uuid)
  if used : id ∈ collection.ids then throw { id } else pure (collection.append id value used)

def duplicateIds (entries : List (Item β)) : List Uuid :=
  let ids := entries.map Item.id
  (ids.filter (ids.count · > 1)).dedup

instance [ToJson β] : ToJson (Collection β) := ⟨(toJson ·.entries)⟩

def duplicateIdsMessage (ids : List Uuid) : String :=
  s!"These ids are shared by more than one item: {", ".intercalate (ids.map (·.value))}. \
    This is a bug in the form data; please contact BLP."

/-- Rejects repeated ids, so a form never opens on such data. -/
def ofEntries (entries : List (Item β)) : Except String (Collection β) :=
  if distinct : (entries.map Item.id).Nodup then .ok { entries, nodup := distinct }
  else .error (duplicateIdsMessage (duplicateIds entries))

instance [FromJson β] : FromJson (Collection β) := ⟨fun json => do ofEntries (← fromJson? json)⟩

end Collection

end Forms.Model
