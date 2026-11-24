module

public import Forms.Model.FreshId
public import Forms.Model.Format
public import Mathlib.Data.List.Dedup

/-!
# Collections

A `Collection β` is an ordered list of entries with distinct ids. The collection owns the ids:
an entry's content `β` has no id of its own, so editing it cannot change or repeat an id.
-/

@[expose] public section
namespace Forms.Model
open Lean

/-- An entry of a collection: its id and its content. -/
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

/-- Reads an entry from a flat object that keeps its id under `idKey`, as upstream records do. -/
def Item.flatFromJson?
  {β : Type}
  [FromJson β]
  (idKey : String)
  (json : Json)
  : Except String (Item β) := do
  let id ← fromJson? (← json.getObjVal? idKey)
  let value ← fromJson? (.obj ((← json.getObj?).erase idKey))
  pure { id, value }

/-- Writes an entry as a flat object with its id under `idKey`. The content must be an object
without that key. -/
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

/-- Entries in order, with distinct ids. -/
structure Collection (β : Type) where
  entries : List (Item β)
  nodup : (entries.map Item.id).Nodup := by decide

namespace Collection

variable {β γ : Type}

theorem ext
  {first second : Collection β}
  (same : first.entries = second.entries)
  : first = second := by
  cases first
  cases second
  cases same
  rfl

instance [DecidableEq β] : DecidableEq (Collection β) := fun first second =>
  decidable_of_iff (first.entries = second.entries) ⟨ext, fun same => same ▸ rfl⟩

def empty : Collection β where
  entries := []
  nodup := List.nodup_nil

def ids (collection : Collection β) : List Uuid :=
  collection.entries.map Item.id

def values (collection : Collection β) : List β :=
  collection.entries.map Item.value

def length (collection : Collection β) : Nat :=
  collection.entries.length

/-- Maps every entry, keeping its id. -/
def mapEntries
  (f : Item β → Item γ)
  (keeps : ∀ item, (f item).id = item.id)
  (collection : Collection β)
  : Collection γ where
  entries := collection.entries.map f
  nodup := by
    rw [List.map_map, show Item.id ∘ f = Item.id from funext keeps]
    exact collection.nodup

def map (f : β → γ) (collection : Collection β) : Collection γ :=
  collection.mapEntries (Item.mapValue f) (Item.id_mapValue f)

/-- Maps every content, given its entry's id. -/
def mapWithId (f : Uuid → β → γ) (collection : Collection β) : Collection γ :=
  collection.mapEntries (fun item => { id := item.id, value := f item.id item.value }) fun _ => rfl

theorem ids_modify
  (entries : List (Item β))
  (index : Nat)
  (f : β → β)
  : (entries.modify index (Item.mapValue f)).map Item.id = entries.map Item.id := by
  apply List.ext_getElem?
  intro position
  simp only [List.getElem?_map, List.getElem?_modify]
  split <;> cases entries[position]? <;> rfl

/-- Applies `f` to the content of the entry at `index`. The ids stay the same. -/
def modifyAt (index : Nat) (f : β → β) (collection : Collection β) : Collection β where
  entries := collection.entries.modify index (Item.mapValue f)
  nodup := by
    rw [ids_modify]
    exact collection.nodup

theorem ids_modifyAt
  (index : Nat)
  (f : β → β)
  (collection : Collection β)
  : (collection.modifyAt index f).ids = collection.ids :=
  ids_modify collection.entries index f

/-- Removes the entry at `index`. -/
def eraseAt (index : Nat) (collection : Collection β) : Collection β where
  entries := collection.entries.eraseIdx index
  nodup := collection.nodup.sublist ((List.eraseIdx_sublist _ _).map _)

/-- Adds an entry at the end. `fresh` keeps the ids distinct. -/
def append
  (id : Uuid)
  (value : β)
  (collection : Collection β)
  (fresh : id ∉ collection.ids)
  : Collection β where
  entries := collection.entries ++ [{ id, value }]
  nodup := by
    rw [List.map_append, List.nodup_append]
    exact ⟨collection.nodup, by simp, by simpa [ids] using fresh⟩

/-- Example data: `values` with the ids `Uuid.ofNat 1`, `Uuid.ofNat 2`, … -/
def numbered
  (values : List β)
  (distinct : ((List.range values.length).map (Uuid.ofNat ·.succ)).Nodup := by decide)
  : Collection β where
  entries := values.mapIdx fun index value => { id := .ofNat index.succ, value }
  nodup := by
    convert distinct using 1
    apply List.ext_getElem <;> simp

/-- A drawn id that the collection already uses. -/
structure IdCollision where
  id : Uuid
  deriving DecidableEq, Repr

/-- Adds `value` with a fresh id. Fresh ids are not proven new, so a clash is reported. -/
def appendFresh
  {m : Type → Type}
  [Monad m]
  [MonadFreshId m]
  (value : β)
  (collection : Collection β)
  : ExceptT IdCollision m (Collection β) := do
  let id ← (freshId : m Uuid)
  if used : id ∈ collection.ids then throw { id } else pure (collection.append id value used)

/-- The ids that more than one entry uses. -/
def duplicateIds (entries : List (Item β)) : List Uuid :=
  let ids := entries.map Item.id
  (ids.filter (ids.count · > 1)).dedup

instance [ToJson β] : ToJson (Collection β) := ⟨(toJson ·.entries)⟩

def duplicateIdsMessage (ids : List Uuid) : String :=
  s!"These ids are shared by more than one item: {", ".intercalate (ids.map (·.value))}. \
    This is a bug in the form data; please contact BLP."

/-- Rejects repeated ids: the form refuses to open on such data. -/
def ofEntries (entries : List (Item β)) : Except String (Collection β) :=
  if distinct : (entries.map Item.id).Nodup then .ok { entries, nodup := distinct }
  else .error (duplicateIdsMessage (duplicateIds entries))

instance [FromJson β] : FromJson (Collection β) := ⟨fun json => do ofEntries (← fromJson? json)⟩

end Collection

end Forms.Model
