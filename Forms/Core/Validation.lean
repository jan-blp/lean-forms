module

public import Forms.Core.Path

@[expose] public section

namespace Forms.Validation

inductive Location : (root : DataType) → Type 1 where
  | self {root : DataType} : Location root
  | field
      {fieldNames : Enum} {fieldTypes : fieldNames → DataType}
      (fieldName : fieldNames)
      (rest : Location (fieldTypes fieldName))
      : Location (.record fieldNames fieldTypes)
  | item {element : DataType}
      (index : Nat)
      (rest : Location element)
      : Location (.list element)
  | constructor
      {tags : Enum} {constructors : tags → DataType}
      (tag : tags)
      (rest : Location (constructors tag))
      : Location (.sum tags constructors)

def Location.exists {root : DataType}
  (location : Location root)
  (value : ⟦root⟧)
  : Bool :=
  match location with
  | .self => true
  | .field name rest => rest.exists (value name)
  | .item index rest =>
      match value[index]? with
      | some element => rest.exists element
      | none => false
  | .constructor tag rest =>
      if h : value.tag = tag then rest.exists (h ▸ value.payload) else false

inductive TargetResolution (root : DataType) where
  | global
  | locations
      (locations : List (Location root))
      (nonempty : locations ≠ [] := by simp)

/-- A location that exists in a particular value. -/
inductive ValidLocation : (root : DataType) → (value : ⟦root⟧) → Type 1 where
  | self {root : DataType} {value : ⟦root⟧} : ValidLocation root value
  | field {fieldNames : Enum} {fieldTypes : fieldNames → DataType}
      {value : ⟦.record fieldNames fieldTypes⟧}
      (name : fieldNames) (rest : ValidLocation (fieldTypes name) (value name))
      : ValidLocation (.record fieldNames fieldTypes) value
  | item {element : DataType} {value : List ⟦element⟧}
      (index : Fin value.length) (rest : ValidLocation element value[index])
      : ValidLocation (.list element) value
  | constructor {tags : Enum} {constructors : tags → DataType}
      {value : ⟦.sum tags constructors⟧}
      (rest : ValidLocation (constructors value.tag) value.payload)
      : ValidLocation (.sum tags constructors) value

def ValidLocation.erase {root : DataType} {value : ⟦root⟧}
    (location : ValidLocation root value) : Location root :=
  match location with
  | .self => .self
  | .field name rest => .field name rest.erase
  | .item index rest => .item index.val rest.erase
  | .constructor (value := selected) rest => .constructor selected.tag rest.erase

theorem ValidLocation.erase_exists {root : DataType} {value : ⟦root⟧}
    (location : ValidLocation root value) : location.erase.exists value = true := by
  induction location with
  | self => rfl
  | field name rest ih => exact ih
  | item index rest ih => simpa [erase, Location.exists] using ih
  | constructor rest ih => simpa [erase, Location.exists] using ih

inductive ValidTargets (root : DataType) (value : ⟦root⟧) where
  | global
  | locations (locations : List (ValidLocation root value))
      (nonempty : locations ≠ [] := by simp)

def ValidTargets.toTargetResolution {root : DataType} {value : ⟦root⟧}
    (targets : ValidTargets root value) : TargetResolution root :=
  match targets with
  | .global => .global
  | .locations locs nonempty => .locations (locs.map (·.erase)) (by simpa using nonempty)

structure ResolvedError (root : DataType) where
  message : String
  targets : TargetResolution root

structure CheckedError (root : DataType) (value : ⟦root⟧) where
  message : String
  targets : ValidTargets root value

def CheckedError.mapLocations {child parent : DataType} {value : ⟦child⟧} {outer : ⟦parent⟧}
    (step : ValidLocation child value → ValidLocation parent outer)
    (error : CheckedError child value) : CheckedError parent outer :=
  { message := error.message
    targets := match error.targets with
      | .global => .global
      | .locations locations nonempty => .locations (locations.map step) (by simpa using nonempty) }

def CheckedError.erase {root : DataType} {value : ⟦root⟧}
    (error : CheckedError root value) : ResolvedError root :=
  { message := error.message, targets := error.targets.toTargetResolution }

abbrev Checker (ty : DataType) := (value : ⟦ty⟧) → List (CheckedError ty value)

/-- A server decision carries either validity or a refutation with an error. -/
inductive ServerDecision {t : DataType}
    (property : ⟦t⟧ → Prop) (value : ⟦t⟧) where
  | valid (proof : property value)
  | invalid (proof : ¬ property value) (message : String) (targets : ValidTargets t value)

abbrev DecidableServerPred {t : DataType} (property : ⟦t⟧ → Prop) :=
  (value : ⟦t⟧) → ServerDecision property value

/-- A property checked only on the server, with evidence for either outcome. -/
structure ServerProperty (ty : DataType) where
  property : ⟦ty⟧ → Prop
  check : DecidableServerPred property

def ServerProperty.errors {ty : DataType} (checked : ServerProperty ty)
    (value : ⟦ty⟧) : List (CheckedError ty value) :=
  match checked.check value with
  | .valid _ => []
  | .invalid _ message targets => [{ message, targets }]

structure CheckedProperty (ty : DataType) where
  property : ⟦ty⟧ → Prop
  checker : Checker ty
  sound : ∀ value, (checker value).isEmpty = true → property value

def CheckedProperty.Complete {ty : DataType} (checked : CheckedProperty ty) : Prop :=
  ∀ value, checked.property value → (checked.checker value).isEmpty = true

def CheckedProperty.ofChecker {ty : DataType}
  (checker : Checker ty)
  : CheckedProperty ty :=
  { property := fun value => (checker value).isEmpty = true
    checker := checker
    sound := fun _ h => h }

theorem CheckedProperty.ofChecker_complete {ty : DataType} (checker : Checker ty) :
    (CheckedProperty.ofChecker checker).Complete :=
  fun _ h => h

@[reducible] def CheckedProperty.require {ty : DataType}
    (property : ⟦ty⟧ → Prop) [DecidablePred property]
    (message : (value : ⟦ty⟧) → String)
    (targets : (value : ⟦ty⟧) → ¬ property value → ValidTargets ty value) : CheckedProperty ty :=
  { property
    checker := fun value => if h : property value then [] else [{ message := message value, targets := targets value h }]
    sound := by intro value h; simpa using h }

@[simp] theorem CheckedProperty.require_complete {ty : DataType}
    {property : ⟦ty⟧ → Prop} [DecidablePred property]
    {message : (value : ⟦ty⟧) → String} {targets : (value : ⟦ty⟧) → ¬ property value → ValidTargets ty value} :
    (CheckedProperty.require property message targets).Complete := by
  intro value h
  change property value at h
  simp [h]

end Forms.Validation

namespace Forms

def Path.validLocation {source target : DataType} (path : Path source target) :
    (value : ⟦source⟧) → Validation.ValidLocation source value :=
  match path with
  | .self => fun _ => .self
  | .field name rest => fun value => .field name (rest.validLocation (value name))

end Forms
