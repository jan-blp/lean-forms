import Forms.Core.Expr

namespace Forms.Validation

/-- A location in `target`, with list indices computed from a value of type `input`. -/
inductive LocationExpr (input : DataType) : (target : DataType) → Type 1 where
  | self {target : DataType} : LocationExpr input target
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

def LocationExpr.eval {input target : DataType}
  (location : LocationExpr input target)
  (context : ⟦input⟧)
  : Location target :=
  match location with
  | .self => .self
  | .field name rest => .field name (rest.eval context)
  | .item index rest => .item (index.eval context) (rest.eval context)
  | .constructor tag rest => .constructor tag (rest.eval context)

def Location.exists {target : DataType}
  (location : Location target)
  (value : ⟦target⟧)
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
  | fields
      (locations : List (Location root))
      (nonempty : locations ≠ [] := by simp)
  | invalidTarget (location : Location root)

inductive TargetsExpr (root input : DataType) where
  | global
  | fields
      (locations : List (LocationExpr input root))
      (nonempty : locations ≠ [] := by simp)

def TargetsExpr.resolve {root input : DataType}
  (targets : TargetsExpr root input)
  (value : ⟦root⟧)
  (context : ⟦input⟧)
  : TargetResolution root :=
  match targets with
  | .global => .global
  | .fields locations nonempty =>
      let resolved := locations.map (·.eval context)
      match resolved.find? (fun location => !location.exists value) with
      | some location => .invalidTarget location
      | none => .fields resolved (by simpa [resolved] using nonempty)

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
      | .fields locations _ => .fields (locations.map step) (by simpa)
      | .invalidTarget location => .invalidTarget (step location) }

inductive IterationField where
  | outer
  | item
  | index
  deriving DecidableEq

instance : FinEnum IterationField :=
  FinEnum.ofList [.outer, .item, .index] (by grind [IterationField])

def iterationFields : Enum where
  type := IterationField
  label
    | .outer => "outer"
    | .item => "item"
    | .index => "index"

abbrev IterationContext (outer element : DataType) : DataType :=
  .record iterationFields fun
    | .outer => outer
    | .item => element
    | .index => .natural

inductive ScopedChecker (root : DataType) : (input : DataType) → Type 1 where
  | pass {input : DataType} : ScopedChecker root input
  | report {input : DataType}
      (message : Expr input .text)
      (targets : TargetsExpr root input)
      : ScopedChecker root input
  | when {input : DataType}
      (condition : Expr input .boolean)
      (body : ScopedChecker root input)
      : ScopedChecker root input
  | seq {input : DataType}
      (left right : ScopedChecker root input)
      : ScopedChecker root input
  | each {input element : DataType}
      (items : Expr input (.list element))
      (body : ScopedChecker root (IterationContext input element))
      : ScopedChecker root input

abbrev Checker (ty : DataType) := ScopedChecker ty ty

def ScopedChecker.eval {root input : DataType}
  (checker : ScopedChecker root input)
  (value : ⟦root⟧)
  (context : ⟦input⟧)
  : List (ResolvedError root) :=
  match checker with
  | .pass => []
  | .report message targets => [{ message := message.eval context, targets := targets.resolve value context }]
  | .when condition body => if condition.eval context then body.eval value context else []
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

/-- A property that's only checked on the server side -/
structure ServerProperty (ty : DataType) where
  property : ⟦ty⟧ → Prop
  decidable : DecidablePred property
  message : ⟦ty⟧ → String
  targets : TargetsExpr ty ty

/-- Infer the decision procedure while requiring explicit error targets. -/
@[reducible] def ServerProperty.require {ty : DataType}
    (property : ⟦ty⟧ → Prop) [decidable : DecidablePred property]
    (message : ⟦ty⟧ → String) (targets : TargetsExpr ty ty) : ServerProperty ty :=
  { property, decidable, message, targets }

def ServerProperty.errors {ty : DataType} (checked : ServerProperty ty)
    (value : ⟦ty⟧) : List (ResolvedError ty) :=
  letI := checked.decidable
  if checked.property value then [] else
    [{ message := checked.message value, targets := checked.targets.resolve value value }]

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
      simpa [Checker.run, ScopedChecker.eval, Expr.eval] using h) }

@[simp] theorem CheckedProperty.require_complete {ty : DataType}
    {property : ⟦ty⟧ → Prop} {condition : Expr ty .boolean} {message : Expr ty .text}
    {targets : TargetsExpr ty ty} {spec : ∀ value, condition.eval value = true ↔ property value} :
    (CheckedProperty.require property condition message targets spec).Complete := by
  intro value h
  simp [Checker.run, ScopedChecker.eval, Expr.eval, (spec value).mpr h]

end Forms.Validation

namespace Forms

def Path.locationExpr {source target input : DataType}
  (path : Path source target)
  : Validation.LocationExpr input source :=
  match path with
  | .self => .self
  | .field name rest => .field name rest.locationExpr

end Forms
