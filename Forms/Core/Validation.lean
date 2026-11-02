import Forms.Core.Expr

namespace Forms.Validation

/-- A location in `root`, with list indices computed from a value of type `input`. -/
inductive LocationExpr (input : DataType) : (root : DataType) → Type 1 where
  | self {root : DataType} : LocationExpr input root
  | field
      {fieldNames : Enum} {fieldTypes : fieldNames → DataType}
      (fieldName : fieldNames)
      (rest : LocationExpr input (fieldTypes fieldName))
      : LocationExpr input (.record fieldNames fieldTypes)
  | item {element : DataType}
      (index : Expr input .natural)
      (rest : LocationExpr input element)
      : LocationExpr input (.list element)
  | constructor
      {tags : Enum} {constructors : tags → DataType}
      (tag : tags)
      (rest : LocationExpr input (constructors tag))
      : LocationExpr input (.sum tags constructors)

/-- `LocationExpr` with evaluated indices. -/
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

def LocationExpr.eval {input root : DataType}
  (location : LocationExpr input root)
  (context : ⟦input⟧)
  : Location root :=
  match location with
  | .self => .self
  | .field name rest => .field name (rest.eval context)
  | .item index rest => .item (index.eval context) (rest.eval context)
  | .constructor tag rest => .constructor tag (rest.eval context)

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
  | invalidTarget (location : Location root)

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

inductive TargetsExpr (root input : DataType) where
  | global
  | locations
      (locations : List (LocationExpr input root))
      (nonempty : locations ≠ [] := by simp)

def TargetsExpr.resolve {root input : DataType}
  (targets : TargetsExpr root input)
  (value : ⟦root⟧)
  (context : ⟦input⟧)
  : TargetResolution root :=
  match targets with
  | .global => .global
  | .locations locs nonempty =>
      let resolved := locs.map (·.eval context)
      match resolved.find? (fun location => !location.exists value) with
      | some location => .invalidTarget location
      | none => .locations resolved (by simpa [resolved] using nonempty)

structure ResolvedError (root : DataType) where
  message : String
  targets : TargetResolution root

def ResolvedError.mapLocations {child parent : DataType}
  (step : Location child → Location parent)
  (error : ResolvedError child)
  : ResolvedError parent :=
  { message := error.message
    targets := match error.targets with
      | .global => .global
      | .locations locs _ => .locations (locs.map step) (by simpa)
      | .invalidTarget location => .invalidTarget (step location) }

inductive BranchField where
  | outer | payload
  deriving DecidableEq

instance : FinEnum BranchField :=
  FinEnum.ofList [.outer, .payload] (by grind [BranchField])

def branchFields : Enum where
  type := BranchField
  label | .outer => "outer" | .payload => "payload"

/-- The selected constructor payload together with the enclosing input. -/
abbrev BranchContext (outer payload : DataType) : DataType :=
  .record branchFields fun
    | .outer => outer
    | .payload => payload

inductive ScopedChecker (root : DataType) : (input : DataType) → Type 1 where
  | pass {input : DataType} : ScopedChecker root input
  | report {input : DataType}
      (message : Expr input .text)
      (targets : TargetsExpr root input)
      : ScopedChecker root input
  | ite {input : DataType}
      (condition : Expr input .boolean)
      (thenBranch elseBranch : ScopedChecker root input)
      : ScopedChecker root input
  | seq {input : DataType}
      (left right : ScopedChecker root input)
      : ScopedChecker root input
  | each {input element : DataType}
      (items : Expr input (.list element))
      (body : ScopedChecker root (IterationContext input element))
      : ScopedChecker root input

  | cases {input : DataType} {tags : Enum} {constructors : tags → DataType}
      (subject : Expr input (.sum tags constructors))
      (branches : (tag : tags) → ScopedChecker root (BranchContext input (constructors tag)))
      : ScopedChecker root input

def ScopedChecker.when {root input : DataType}
    (condition : Expr input .boolean)
    (body : ScopedChecker root input) : ScopedChecker root input :=
  .ite condition body .pass

abbrev Checker (ty : DataType) := ScopedChecker ty ty

def ScopedChecker.eval {root input : DataType}
  (checker : ScopedChecker root input)
  (value : ⟦root⟧)
  (context : ⟦input⟧)
  : List (ResolvedError root) :=
  match checker with
  | .pass => []
  | .report message targets => [{ message := message.eval context, targets := targets.resolve value context }]
  | .ite condition thenBranch elseBranch =>
    if condition.eval context then thenBranch.eval value context else elseBranch.eval value context
  | .cases subject branches =>
    let selected := subject.eval context
    (branches selected.tag).eval value fun
      | .outer => context
      | .payload => selected.payload
  | .seq left right => left.eval value context ++ right.eval value context
  | .each items body =>
      (items.eval context).zipIdx.flatMap fun (item, index) =>
        body.eval value fun
          | .outer => context
          | .item => item
          | .index => index

def Checker.run {ty : DataType}
  (checker : Checker ty)
  (value : ⟦ty⟧)
  : List (ResolvedError ty) :=
  checker.eval value value

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
    (value : ⟦ty⟧) : List (ResolvedError ty) :=
  match checked.check value with
  | .valid _ => []
  | .invalid _ message targets => [{ message, targets := targets.toTargetResolution }]

structure CheckedProperty (ty : DataType) where
  property : ⟦ty⟧ → Prop
  checker : Checker ty
  sound : ∀ value, (checker.run value).isEmpty = true → property value

def CheckedProperty.Complete {ty : DataType} (checked : CheckedProperty ty) : Prop :=
  ∀ value, checked.property value → (checked.checker.run value).isEmpty = true

def CheckedProperty.ofChecker {ty : DataType}
  (checker : Checker ty)
  : CheckedProperty ty :=
  { property := fun value => (checker.run value).isEmpty = true
    checker := checker
    sound := fun _ h => h }

theorem CheckedProperty.ofChecker_complete {ty : DataType} (checker : Checker ty) :
    (CheckedProperty.ofChecker checker).Complete :=
  fun _ h => h

/-- Builds a checked property from an equivalent Boolean condition. -/
@[reducible] def CheckedProperty.require {ty : DataType}
  (property : ⟦ty⟧ → Prop)
  (condition : Expr ty .boolean)
  (message : Expr ty .text)
  (targets : TargetsExpr ty ty)
  (spec : ∀ value, condition.eval value = true ↔ property value := by
    intro value; grind [Expr.eval, Path.get])
  : CheckedProperty ty :=
  { property
    checker := .when (.not condition) (.report message targets)
    sound := fun value h => (spec value).mp (by
      simpa [Checker.run, ScopedChecker.eval, ScopedChecker.when, Expr.eval] using h) }

@[simp] theorem CheckedProperty.require_complete {ty : DataType}
    {property : ⟦ty⟧ → Prop} {condition : Expr ty .boolean} {message : Expr ty .text}
    {targets : TargetsExpr ty ty} {spec : ∀ value, condition.eval value = true ↔ property value} :
    (CheckedProperty.require property condition message targets spec).Complete := by
  intro value h
  simp [Checker.run, ScopedChecker.eval, ScopedChecker.when, Expr.eval, (spec value).mpr h]

end Forms.Validation

namespace Forms

def Path.locationExpr {source target input : DataType}
  (path : Path source target)
  : Validation.LocationExpr input source :=
  match path with
  | .self => .self
  | .field name rest => .field name rest.locationExpr

end Forms
