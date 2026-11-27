module

public import Lean.Data.Json
public import Forms.Model.ErasedLocation
public import Forms.Model.Collection
public import Forms.Model.Lens
public import Forms.Model.LawfulJson
public import LeanLens.Lawful
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.OfFn
public import Std.Data.HashMap
open LeanLens

@[expose] public section
namespace Forms.Model

class Fields (α : Type) where
  Field : Type → Type
  lens : {β : Type} → Field β → Lens' α β
  lawful : ∀ {β} (field : Field β), LawfulLens (lens field)
  /-- The field name used in serialization. -/
  key : {β : Type} → Field β → String

attribute [reducible] Fields.Field

def Fields.get {α β : Type} [Fields α] (field : Fields.Field α β) : α → β :=
  LeanLens.view (Fields.lens field)

def Fields.set
  {α β : Type}
  [Fields α]
  (field : Fields.Field α β)
  : β → α → α :=
  LeanLens.set (Fields.lens field)

/-- Keys sent to the client and decoded back; `""` is reserved for no selection. -/
class Key (Value : Type) where
  encode : Value → String
  decode : String → Option Value
  decode_encode : ∀ key, decode (encode key) = some key
  encode_ne_empty : ∀ key, encode key ≠ ""

theorem Key.encode_injective
  {Key : Type}
  [Forms.Model.Key Key]
  : Function.Injective (Forms.Model.Key.encode (Value := Key)) := by
  intro first second h
  simpa [Forms.Model.Key.decode_encode] using congrArg (Forms.Model.Key.decode (Value := Key)) h

theorem Key.find?_encode
  {Key : Type}
  (encode : Key → String)
  : ∀ (all : List Key) (key : Key), key ∈ all → (all.map encode).Nodup →
    all.find? (encode · == encode key) = some key
  | [], _, member, _ => nomatch member
  | head :: rest, key, member, nodup => by
    rw [List.map_cons, List.nodup_cons] at nodup
    rcases List.mem_cons.mp member with same | later
    · subst same
      simp
    · by_cases clash : encode head = encode key
      · exact absurd (clash ▸ List.mem_map_of_mem later) nodup.1
      · simp [clash, Forms.Model.Key.find?_encode encode rest key later nodup.2]

theorem Key.isChain_of_toList
  : ∀ {names : List String}, (names.map String.toList).IsChain (· < ·) → names.IsChain (· < ·)
  | [], _ => .nil
  | [_], _ => .singleton _
  | _ :: _ :: _, .cons_cons less rest =>
    .cons_cons
      (String.toByteArray_lt_toByteArray_iff.mp
        (String.toList_lt_toList_iff_toByteArray_lt_toByteArray.mp less))
      (isChain_of_toList rest)

/-- Decodes by looking names up in `all`. Its names strictly increase, so checking them takes
one comparison per key rather than one per pair. -/
@[instance_reducible] def Key.ofSorted
  {Key : Type}
  (all : List Key)
  (encode : Key → String)
  (complete : ∀ key, key ∈ all)
  (sorted : (all.map encode).IsChain (· < ·))
  (named : ∀ name ∈ all.map encode, name ≠ "")
  : Forms.Model.Key Key where
  encode
  decode name := all.find? (encode · == name)
  decode_encode key :=
    haveI : Trans (α := String) (· < ·) (· < ·) (· < ·) := ⟨Std.lt_trans⟩
    Forms.Model.Key.find?_encode encode all key (complete key)
      (sorted.pairwise.imp (S := (· ≠ ·)) fun {first second} (less : first < second) same =>
        Std.lt_irrefl (same ▸ less))
  encode_ne_empty key := named (encode key) (List.mem_map_of_mem (complete key))

class Constructors (α : Type) where
  Constructor : Type → Type
  /-- Names a constructor regardless of its payload. -/
  Tag : Type
  [tagDecidableEq : DecidableEq Tag]
  [tagKey : Key Tag]
  inject : {β : Type} → Constructor β → β → α
  project : {β : Type} → Constructor β → α → Option β
  tagOf : {β : Type} → Constructor β → Tag
  tag : α → Tag

attribute [reducible] Constructors.Constructor Constructors.Tag

instance {α : Type} [Constructors α] : DecidableEq (Constructors.Tag α) :=
  Constructors.tagDecidableEq

instance {α : Type} [Constructors α] : Key (Constructors.Tag α) :=
  Constructors.tagKey

def Constructors.key {α β : Type} [Constructors α] (constructor : Constructor α β) : String :=
  Forms.Model.Key.encode (tagOf constructor)

class LawfulConstructors (α : Type) [Constructors α] : Prop where
  project_inject : ∀ {β : Type} (c : Constructors.Constructor α β) (value : β),
    Constructors.project c (Constructors.inject c value) = some value
  inject_project : ∀ {β : Type} (c : Constructors.Constructor α β) (source : α) (value : β),
    Constructors.project c source = some value → Constructors.inject c value = source
  tag_inject : ∀ {β : Type} (c : Constructors.Constructor α β) (value : β),
    Constructors.tag (Constructors.inject c value) = Constructors.tagOf c

inductive Path : Type → Type → Type 1 where
  | self {α : Type} : Path α α
  | stepField
      {α β γ : Type}
      [fields : Fields α]
      (field : Fields.Field α β)
      (rest : Path β γ)
      : Path α γ

macro "path[" fields:term,* "]" : term => do
  let mut result ← `(Path.self)
  for field in fields.getElems.reverse do
    result ← `(Path.stepField (field := $field) (rest := $result))
  return result

def Path.get {α β : Type} (path : Path α β) (value : α) : β :=
  match path with
  | .self => value
  | .stepField (fields := _) f rest => rest.get (Fields.get f value)

def Path.set
  {α β : Type}
  (path : Path α β)
  (new : β)
  (value : α)
  : α :=
  match path with
  | .self => new
  | .stepField (fields := _) f rest => Fields.set f (rest.set new (Fields.get f value)) value

def Path.trans
  {α β γ : Type}
  (first : Path α β)
  (second : Path β γ)
  : Path α γ :=
  match first with
  | .self => second
  | .stepField (fields := _) f rest => .stepField f (rest.trans second)

def Path.erase {α β : Type} : Path α β → ErasedLocation
  | .self => []
  | .stepField (fields := _) f rest => .field (Fields.key f) :: rest.erase

def Path.toLens {α β : Type} (path : Path α β) : Lens' α β :=
  LeanLens.mkLens path.get path.set

-- TODO: define as a `PartialPath` known to resolve in `value`
inductive Location : {α : Type} → α → Type 1 where
  | self {α : Type} {value : α} : Location value
  | field
      {α β : Type}
      [fields : Fields α]
      {value : α}
      (field : Fields.Field α β)
      (rest : Location (Fields.get field value))
      : Location value
  | constructor
      {α β : Type}
      [constructors : Constructors α]
      {value : β}
      (constructor : Constructors.Constructor α β)
      (rest : Location value)
      : Location (Constructors.inject constructor value)
  | item
      {α : Type}
      {items : Collection α}
      (entry : Item α)
      (member : entry ∈ items.entries)
      (rest : Location entry.value)
      : Location items

def Location.keys {α : Type} {value : α} : Location value → List String
  | .self => []
  | .field (fields := _) f rest => Fields.key f :: rest.keys
  | .constructor (constructors := _) c rest => Constructors.key c :: rest.keys
  | .item (items := items) entry _ rest => entry.id.value :: rest.keys

def Location.erase {α : Type} {value : α} : Location value → ErasedLocation
  | .self => []
  | .field (fields := _) f rest => .field (Fields.key f) :: rest.erase
  | .constructor (constructors := _) c rest => .constructor (Constructors.key c) :: rest.erase
  | .item (items := items) entry _ rest => .item entry.id :: rest.erase

inductive Targets (α : Type) (value : α) where
  | global
  | locations (first : Location value) (rest : List (Location value) := [])

syntax locationPath := sepBy1(term:max, " / ")

/-- `locations[a / b, c]` targets the field paths `a / b` and `c`. -/
macro "locations[" paths:sepBy1(locationPath, ", ") "]" : term => do
  let locations ← paths.getElems.mapM fun path => do
    let mut result ← `(Location.self)
    for field in path.raw[0].getSepArgs.reverse do
      result ← `(Location.field (field := $(⟨field⟩)) (rest := $result))
    return result
  let rest := locations.extract 1 locations.size
  `(Targets.locations (first := $(locations[0]!)) (rest := [$rest,*]))

structure Error {α : Type} (value : α) where
  message : String
  targets : Targets α value

def Targets.mapLocations
  {α β : Type}
  {a : α}
  {b : β}
  (move : Location a → Location b)
  : Targets α a → Targets β b
  | .global => .locations (move .self)
  | .locations first rest => .locations (move first) (rest.map move)

def Error.mapLocations
  {α β : Type}
  {value : α}
  {outer : β}
  (step : Location value → Location outer)
  (error : Error value)
  : Error outer where
  message := error.message
  targets := error.targets.mapLocations step

def Error.lift
  {α β : Type}
  [Fields α]
  {value : α}
  (field : Fields.Field α β)
  (error : Error (Fields.get field value))
  : Error value :=
  error.mapLocations (.field field)

def Error.inConstructor
  {α β : Type}
  [Constructors α]
  {value : β}
  (constructor : Constructors.Constructor α β)
  (error : Error value)
  : Error (Constructors.inject constructor value) :=
  error.mapLocations (.constructor constructor)

inductive Decision (property : Prop) {α : Type} (value : α) where
  | valid (proof : property)
  | invalid (proof : ¬ property) (message : String) (targets : Targets α value)

def Decision.errors
  {property : Prop}
  {α : Type}
  {value : α}
  : Decision property value → List (Error value)
  | .valid _ => []
  | .invalid _ message targets => [{ message, targets }]

def Decision.toExcept
  {property : Prop}
  {α : Type}
  {value raw : α}
  (decision : Decision property value)
  (equality : value = raw)
  : Except (List (Error raw)) (PLift property) :=
  match decision with
  | .valid proof => .ok ⟨proof⟩
  | .invalid .. => .error (equality ▸ decision.errors)

class Constraints (constraint : Type) where
  Parts : constraint → Type
  Raw : constraint → Type
  toRaw : (c : constraint) → Parts c → Raw c
  holds : (c : constraint) → Parts c → Prop

attribute [reducible] Constraints.Parts Constraints.Raw Constraints.toRaw Constraints.holds

class ConstraintRule {constraint : Type} [Constraints constraint] (c : constraint) where
  check : (parts : Constraints.Parts c) →
    Decision (Constraints.holds c parts) (Constraints.toRaw c parts)

end Forms.Model

class FormModel (model : Type) where
  Raw : Type
  erase : model → Raw

attribute [reducible] FormModel.Raw

namespace Forms.Model

abbrev Raw (α : Type) [FormModel α] : Type :=
  FormModel.Raw α

abbrev Validated (model : Type) [FormModel model] (raw : Raw model) :=
  { value : model // FormModel.erase value = raw }

class Validation (model : Type) [FormModel model] where
  validate : (raw : Raw model) → Except (List (Error raw)) (Validated model raw)

def errors {α β : Type _} : Except (List α) β → List α
  | .ok _ => []
  | .error errors => errors

/-- Applies `f` to `x` if both succeed, else collects the errors of both. -/
def accumulate
  {ε : Type _}
  {α β : Type _}
  (f : Except (List ε) (α → β))
  (x : Except (List ε) α)
  : Except (List ε) β :=
  match f, x with
  | .ok f, .ok x => .ok (f x)
  | f, x => .error (errors f ++ errors x)

@[reducible] instance : FormModel String := ⟨String, id⟩
@[reducible] instance : FormModel Bool := ⟨Bool, id⟩
@[reducible] instance : FormModel Nat := ⟨Nat, id⟩
@[reducible] instance : FormModel Int := ⟨Int, id⟩
@[reducible] instance : FormModel Int32 := ⟨Int32, id⟩
@[reducible] instance : FormModel Int64 := ⟨Int64, id⟩
@[reducible] instance : FormModel Decimal := ⟨Decimal, id⟩
@[reducible] instance : FormModel Std.Time.PlainDate := ⟨Std.Time.PlainDate, id⟩
@[reducible] instance : FormModel Uuid := ⟨Uuid, id⟩
instance : Validation String := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Bool := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Nat := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Int := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Int32 := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Int64 := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Decimal := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Std.Time.PlainDate := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Uuid := ⟨fun value => .ok ⟨value, rfl⟩⟩

@[reducible] instance {α : Type} [FormModel α] : FormModel (List α) :=
  ⟨List (Raw α), List.map FormModel.erase⟩

@[reducible] instance {α : Type} [FormModel α] : FormModel (Collection α) :=
  ⟨Collection (Raw α), Collection.map FormModel.erase⟩

/-- Validates every entry's content; errors point at their entry's id. -/
instance {α : Type} [FormModel α] [Validation α] : Validation (Collection α) where
  validate raw :=
    let entries := raw.entries
    let results (position : Fin entries.length) :=
      Validation.validate (model := α) (entries.get position).value
    if valid : ∀ position, (results position).isOk then
      let values (position : Fin entries.length) : Validated α (entries.get position).value :=
        match results position, valid position with
        | .ok value, _ => value
        | .error _, h => nomatch h
      let validated : List (Item α) := List.ofFn fun position =>
        { id := (entries.get position).id, value := (values position).val }
      have ids : validated.map Item.id = entries.map Item.id := by
        simp [validated, List.map_ofFn, Function.comp_def, List.ofFn_getElem_eq_map]
      .ok ⟨{ entries := validated, nodup := ids ▸ raw.nodup }, Collection.ext (by
        simp [validated, FormModel.erase, Collection.map, Collection.mapEntries, Item.mapValue,
          List.map_ofFn, Function.comp_def, (values _).property, entries])⟩
    else
      .error ((List.finRange entries.length).flatMap fun position =>
        (errors (results position)).map
          (Error.mapLocations (.item (entries.get position) (List.get_mem entries position))))

/-- A model whose raw values are all valid. -/
class AlwaysValid (α : Type) [FormModel α] where
  restore : Raw α → α
  erase_restore : ∀ raw, FormModel.erase (restore raw) = raw
  restore_erase : ∀ value, restore (FormModel.erase value) = value

theorem nodup_map_of_inverse
  {α β : Type}
  {items : List α}
  (f : β → α)
  (g : α → β)
  (inverse : ∀ value, f (g value) = value)
  (nodup : items.Nodup)
  : (items.map g).Nodup := by
  unfold List.Nodup at *
  exact List.Pairwise.map g (fun _ _ distinct same => distinct (by
    simpa [inverse] using congrArg f same)) nodup

@[reducible] instance {α : Type} [FormModel α] [AlwaysValid α]
    : FormModel { items : List α // items.Nodup } :=
  ⟨{ items : List (Raw α) // items.Nodup }, fun items =>
    ⟨items.1.map FormModel.erase, nodup_map_of_inverse _ _ AlwaysValid.restore_erase items.2⟩⟩

instance {α : Type} [FormModel α] [AlwaysValid α]
    : Validation { items : List α // items.Nodup } where
  validate raw :=
    .ok ⟨⟨raw.1.map AlwaysValid.restore, nodup_map_of_inverse _ _ AlwaysValid.erase_restore raw.2⟩,
      Subtype.ext (by simp [FormModel.erase, Function.comp_def, AlwaysValid.erase_restore])⟩

instance {α : Type} [Lean.ToJson α] : Lean.ToJson { items : List α // items.Nodup } :=
  ⟨(Lean.toJson ·.1)⟩

instance {α : Type} [Lean.FromJson α] [DecidableEq α]
    : Lean.FromJson { items : List α // items.Nodup } :=
  ⟨fun json => do
    let items : List α ← Lean.fromJson? json
    if distinct : items.Nodup then return ⟨items, distinct⟩ else throw "Expected distinct items."⟩

inductive OptionConstructor (α : Type) : Type → Type where
  | none : OptionConstructor α Unit
  | some : OptionConstructor α α

inductive OptionTag where
  | none
  | some
  deriving DecidableEq, Repr

instance : Key OptionTag where
  encode
    | .none => "none"
    | .some => "some"
  decode
    | "none" => some .none
    | "some" => some .some
    | _ => none
  decode_encode tag := by cases tag <;> rfl
  encode_ne_empty tag := by cases tag <;> decide

@[reducible] instance {α : Type} : Constructors (Option α) where
  Constructor := OptionConstructor α
  Tag := OptionTag
  inject
    | .none, () => none
    | .some, value => some value
  project
    | .none, none => some ()
    | .none, some _ => none
    | .some, value => value
  tagOf
    | .none => .none
    | .some => .some
  tag
    | none => .none
    | some _ => .some

instance {α : Type} : LawfulConstructors (Option α) where
  project_inject selected value := by cases selected <;> rfl
  inject_project selected source value h := by
    cases selected <;> cases source <;> simp_all [Constructors.project, Constructors.inject]
  tag_inject selected value := by cases selected <;> rfl

@[reducible] instance {α : Type} [FormModel α] : FormModel (Option α) :=
  ⟨Option (Raw α), Option.map FormModel.erase⟩

instance {α : Type} [FormModel α] [Validation α] : Validation (Option α) where
  validate
    | none => .ok ⟨none, rfl⟩
    | some raw => match Validation.validate (model := α) raw with
      | .ok ⟨value, erased⟩ => .ok ⟨some value, by simp [FormModel.erase, erased]⟩
      | .error errors =>
        .error (errors.map (Error.inConstructor (α := Option (Raw α)) OptionConstructor.some))

end Forms.Model
