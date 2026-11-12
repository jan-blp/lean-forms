module

public import Lean.Data.Json
public import LeanLens.Lawful
public import Std.Data.HashMap
open LeanLens

@[expose] public section
namespace Forms.Model

/-- Describes a record's typed fields. -/
class Fields (α : Type) where
  Field : Type → Type
  lens : {β : Type} → Field β → Lens' α β
  lawful : ∀ {β} (field : Field β), LawfulLens (lens field)
  /-- The field name used in serialization . -/
  key : {β : Type} → Field β → String
  key_injective : ∀ {β γ : Type} (a : Field β) (b : Field γ), key a = key b → a ≍ b

attribute [reducible] Fields.Field

def Fields.get {α β : Type} [Fields α] (field : Fields.Field α β) : α → β :=
  LeanLens.view (Fields.lens field)

def Fields.set
  {α β : Type}
  [Fields α]
  (field : Fields.Field α β)
  : β → α → α :=
  LeanLens.set (Fields.lens field)

/-- Describes a sum type's constructors. -/
class Constructors (α : Type) where
  Constructor : Type → Type
  inject : {β : Type} → Constructor β → β → α
  /-- The payload of a value built by `constructor`. -/
  project : {β : Type} → Constructor β → α → Option β
  key : {β : Type} → Constructor β → String

attribute [reducible] Constructors.Constructor

/-- Constructor injection and projection describe the same payload. -/
class LawfulConstructors (α : Type) [Constructors α] : Prop where
  project_inject : ∀ {β : Type} (c : Constructors.Constructor α β) (value : β),
    Constructors.project c (Constructors.inject c value) = some value
  inject_project : ∀ {β : Type} (c : Constructors.Constructor α β) (source : α) (value : β),
    Constructors.project c source = some value → Constructors.inject c value = source

inductive Path : Type → Type → Type 1 where
  | self {α : Type} : Path α α
  | stepField
      {α β γ : Type}
      [Fields α]
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
  | @stepField _ _ _ inst f rest => rest.get (@Fields.get _ _ inst f value)

def Path.set
  {α β : Type}
  (path : Path α β)
  (new : β)
  (value : α)
  : α :=
  match path with
  | .self => new
  | @stepField _ _ _ inst f rest =>
    @Fields.set _ _ inst f (rest.set new (@Fields.get _ _ inst f value)) value

def Path.trans
  {α β γ : Type}
  (first : Path α β)
  (second : Path β γ)
  : Path α γ :=
  match first with
  | .self => second
  | @stepField _ _ _ inst f rest => @Path.stepField _ _ _ inst f (rest.trans second)

def Path.toLens {α β : Type} (path : Path α β) : Lens' α β :=
  LeanLens.mkLens path.get path.set

inductive Location : {α : Type} → α → Type 1 where
  | self {α : Type} {value : α} : Location value
  | field
      {α β : Type}
      [Fields α]
      {value : α}
      (field : Fields.Field α β)
      (rest : Location (Fields.get field value))
      : Location value
  | constructor
      {α β : Type}
      [Constructors α]
      {value : β}
      (constructor : Constructors.Constructor α β)
      (rest : Location value)
      : Location (Constructors.inject constructor value)
  | index
      {α : Type}
      {value : List α}
      (position : Fin value.length)
      (rest : Location (value.get position))
      : Location value

def Location.keys {α : Type} {value : α} : Location value → List String
  | .self => []
  | @field _ _ inst _ f rest => @Fields.key _ inst _ f :: rest.keys
  | @constructor _ _ inst _ c rest => @Constructors.key _ inst _ c :: rest.keys
  | index position rest => toString position.val :: rest.keys

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

def Error.mapLocations
  {α β : Type}
  {value : α}
  {outer : β}
  (step : Location value → Location outer)
  (error : Error value)
  : Error outer where
  message := error.message
  targets := match error.targets with
    | .global => .locations (step .self)
    | .locations first rest => .locations (step first) (rest.map step)

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

abbrev Validated (model : Type) [FormModel model] (raw : FormModel.Raw model) :=
  { value : model // FormModel.erase value = raw }

class Validation (model : Type) [FormModel model] where
  validate : (raw : FormModel.Raw model) → Except (List (Error raw)) (Validated model raw)

def errors {α β : Type _} : Except (List α) β → List α
  | .ok _ => []
  | .error errors => errors

@[reducible] instance : FormModel String := ⟨String, id⟩
@[reducible] instance : FormModel Bool := ⟨Bool, id⟩
@[reducible] instance : FormModel Nat := ⟨Nat, id⟩
instance : Validation String := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Bool := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Nat := ⟨fun value => .ok ⟨value, rfl⟩⟩

@[reducible] instance {α : Type} [FormModel α] : FormModel (List α) :=
  ⟨List (FormModel.Raw α), List.map FormModel.erase⟩

/-- Validates every item; errors point at their item's position. -/
instance {α : Type} [FormModel α] [Validation α] : Validation (List α) where
  validate raw :=
    let results (position : Fin raw.length) := Validation.validate (model := α) (raw.get position)
    if valid : ∀ position, (results position).isOk then
      let values (position : Fin raw.length) : Validated α (raw.get position) :=
        match results position, valid position with
        | .ok value, _ => value
        | .error _, h => nomatch h
      .ok ⟨List.ofFn fun position => (values position).val, by
        simp [FormModel.erase, Function.comp_def, (values _).property]⟩
    else
      .error ((List.finRange raw.length).flatMap fun position =>
        (errors (results position)).map (Error.mapLocations (.index position)))

end Forms.Model
