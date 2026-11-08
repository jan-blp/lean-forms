module

public import Lean.Data.Json
public import LeanLens.Lawful

@[expose] public section
namespace Forms.Model

class Fields (raw : Type) where
  Field : Type → Type
  lens : {value : Type} → Field value → LeanLens.Lens' raw value
  lawful : ∀ {value} (field : Field value), LeanLens.LawfulLens (lens field)
  /-- The field name used in serialization . -/
  key : {value : Type} → Field value → String
  key_injective : ∀ {α β : Type} (a : Field α) (b : Field β), key a = key b → a ≍ b

attribute [reducible] Fields.Field

def Fields.get {raw value : Type} [Fields raw] (field : Fields.Field raw value) : raw → value :=
  LeanLens.view (Fields.lens field)

def Fields.set {raw value : Type} [Fields raw] (field : Fields.Field raw value) : value → raw → raw :=
  LeanLens.set (Fields.lens field)

class Constructors (raw : Type) where
  Constructor : Type → Type
  inject : {payload : Type} → Constructor payload → payload → raw
  key : {payload : Type} → Constructor payload → String

attribute [reducible] Constructors.Constructor

inductive Path : Type → Type → Type 1 where
  | self {value : Type} : Path value value
  | stepField {source child target : Type} [Fields source]
      (field : Fields.Field source child)
      (rest : Path child target)
      : Path source target

def Path.field {source value : Type} [Fields source]
    (field : Fields.Field source value) : Path source value :=
  .stepField (field := field) (rest := .self)

def Path.get {source target : Type} (path : Path source target) (value : source) : target :=
  match path with
  | .self => value
  | @stepField _ _ _ inst f rest => rest.get (@Fields.get _ _ inst f value)

def Path.set {source target : Type} (path : Path source target) (new : target) (value : source) : source :=
  match path with
  | .self => new
  | @stepField _ _ _ inst f rest =>
    @Fields.set _ _ inst f (rest.set new (@Fields.get _ _ inst f value)) value

def Path.trans {source middle target : Type} (first : Path source middle)
    (second : Path middle target) : Path source target :=
  match first with
  | .self => second
  | @stepField _ _ _ inst f rest => @Path.stepField _ _ _ inst f (rest.trans second)

theorem Path.get_set {source target : Type} (path : Path source target) (new : target) (value : source) :
    path.get (path.set new value) = new := by
  induction path with
  | self => rfl
  | @stepField source child target inst f rest ih =>
    simp only [get, set, Fields.get, Fields.set, (Fields.lawful f).view_set]
    exact ih _ _

theorem Path.set_get {source target : Type} (path : Path source target) (value : source) :
    path.set (path.get value) value = value := by
  induction path with
  | self => rfl
  | @stepField source child target inst f rest ih =>
    simp only [get, set, ih, Fields.get, Fields.set, (Fields.lawful f).set_view]

theorem Path.set_set {source target : Type} (path : Path source target)
    (first second : target) (value : source) :
    path.set second (path.set first value) = path.set second value := by
  induction path with
  | self => rfl
  | @stepField source child target inst f rest ih =>
    simp only [set, Fields.get, Fields.set, (Fields.lawful f).view_set, ih,
      (Fields.lawful f).set_set]

def Path.toLens {source target : Type} (path : Path source target) : LeanLens.Lens' source target :=
  LeanLens.mkLens path.get path.set

instance {source target : Type} (path : Path source target) : LeanLens.LawfulLens path.toLens where
  view_set := path.get_set
  set_view := path.set_get
  set_set := path.set_set

inductive Location : (raw : Type) → raw → Type 1 where
  | self {raw : Type} {value : raw} : Location raw value
  | field {raw child : Type} [Fields raw] {value : raw}
      (field : Fields.Field raw child)
      (rest : Location child (Fields.get field value)) : Location raw value
  | constructor {raw payload : Type} [Constructors raw] {value : payload}
      (constructor : Constructors.Constructor raw payload) (rest : Location payload value) :
      Location raw (Constructors.inject constructor value)

def Location.keys {raw : Type} {value : raw} : Location raw value → List String
  | .self => []
  | @field _ _ inst _ f rest => @Fields.key _ inst _ f :: rest.keys
  | @constructor _ _ inst _ c rest => @Constructors.key _ inst _ c :: rest.keys

inductive Targets (raw : Type) (value : raw) where
  | global
  | locations (first : Location raw value) (rest : List (Location raw value) := [])

structure Error {raw : Type} (value : raw) where
  message : String
  targets : Targets raw value

def Error.mapLocations {source target : Type} {value : source} {outer : target}
    (step : Location source value → Location target outer) (error : Error value) : Error outer where
  message := error.message
  targets := match error.targets with
    | .global => .locations (step .self)
    | .locations first rest => .locations (step first) (rest.map step)

def Error.lift {raw child : Type} [Fields raw] {value : raw}
    (field : Fields.Field raw child) (error : Error (Fields.get field value)) : Error value :=
  error.mapLocations (.field field)

def Error.inConstructor {raw payload : Type} [Constructors raw] {value : payload}
    (constructor : Constructors.Constructor raw payload) (error : Error value) :
    Error (Constructors.inject constructor value) :=
  error.mapLocations (.constructor constructor)

inductive Decision (property : Prop) {raw : Type} (value : raw) where
  | valid (proof : property)
  | invalid (proof : ¬ property) (message : String) (targets : Targets raw value)

def Decision.errors {property : Prop} {raw : Type} {value : raw} :
    Decision property value → List (Error value)
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

def errors {error value : Type _} : Except (List error) value → List error
  | .ok _ => []
  | .error errors => errors

@[reducible] instance : FormModel String := ⟨String, id⟩
@[reducible] instance : FormModel Bool := ⟨Bool, id⟩
@[reducible] instance : FormModel Nat := ⟨Nat, id⟩
instance : Validation String := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Bool := ⟨fun value => .ok ⟨value, rfl⟩⟩
instance : Validation Nat := ⟨fun value => .ok ⟨value, rfl⟩⟩

end Forms.Model
