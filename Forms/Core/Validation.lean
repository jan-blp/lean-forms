import Forms.Core.Expr

namespace Forms.Validation

inductive LocationStep where
  | field (name : String)
  | item (index : Nat)
  | constructor (tag : String)
  deriving BEq, Repr

abbrev Location := List LocationStep

inductive Targets where
  | global
  | fields
      (locations : List Location)
      (nonempty : locations ≠ [] := by simp)

structure ValidationError where
  message : String
  targets : Targets

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

inductive LocationStepExpr (input : DataType) where
  | field (name : String)
  | item (index : Expr input .natural)
  | constructor (tag : Expr input .text)

abbrev LocationExpr (input : DataType) := List (LocationStepExpr input)

inductive TargetsExpr (input : DataType) where
  | global
  | fields
      (locations : List (LocationExpr input))
      (nonempty : locations ≠ [] := by simp)

inductive Checker : DataType → Type 1 where
  | pass {input : DataType} : Checker input
  | report {input : DataType}
      (message : Expr input .text)
      (targets : TargetsExpr input)
      : Checker input
  | when {input : DataType}
      (condition : Expr input .boolean)
      (body : Checker input)
      : Checker input
  | seq {input : DataType}
      (left right : Checker input)
      : Checker input
  | each {input element : DataType}
      (items : Expr input (.list element))
      (body : Checker (IterationContext input element))
      : Checker input

def LocationStepExpr.eval {input : DataType}
  (step : LocationStepExpr input)
  (value : ⟦input⟧)
  : LocationStep :=
  match step with
  | .field name => .field name
  | .item index => .item (index.eval value)
  | .constructor tag => .constructor (tag.eval value)

def TargetsExpr.eval {input : DataType}
  (targets : TargetsExpr input)
  (value : ⟦input⟧)
  : Targets :=
  match targets with
  | .global => .global
  | .fields locations nonempty =>
      .fields (locations.map fun location => location.map fun step => step.eval value)
        (nonempty := by intro h; exact nonempty (List.map_eq_nil_iff.mp h))

def Checker.eval {input : DataType}
  (checker : Checker input)
  (value : ⟦input⟧)
  : List ValidationError :=
  match checker with
  | .pass => []
  | .report message targets => [{ message := message.eval value, targets := targets.eval value }]
  | .when condition body => if condition.eval value then body.eval value else []
  | .seq left right => left.eval value ++ right.eval value
  | .each items body =>
      (items.eval value).zipIdx.flatMap fun (item, index) =>
        body.eval fun
          | .outer => value
          | .item => item
          | .index => index

def Location.exists
  (location : Location)
  (ty : DataType)
  (value : ⟦ty⟧)
  : Bool :=
  match location with
  | [] => true
  | step :: rest =>
      match ty with
      | .record names types =>
          match step with
          | .field name => (FinEnum.toList names).any fun field =>
              names.label field == name && Location.exists rest (types field) (value field)
          | .item _ => false
          | .constructor _ => false
      | .list element =>
          match step with
          | .item index =>
              match value[index]? with
              | none => false
              | some item => Location.exists rest element item
          | .field _ => false
          | .constructor _ => false
      | .sum tags constructors =>
          match step with
          | .constructor tag =>
              tags.label value.tag == tag && Location.exists rest (constructors value.tag) value.payload
          | .field _ => false
          | .item _ => false
      | .text => false
      | .boolean => false
      | .natural => false
      | .date => false
      | .enum _ => false

inductive TargetResolution where
  | global
  | fields
      (locations : List Location)
      (nonempty : locations ≠ [] := by simp)
  | invalidTarget (location : Location)

structure ResolvedError where
  message : String
  targets : TargetResolution

def ResolvedError.prefix
  (step : LocationStep)
  (error : ResolvedError)
  : ResolvedError :=
  { message := error.message
    targets := match error.targets with
      | .global => .global
      | .fields locations _ => .fields (locations.map (step :: ·)) (by simpa)
      | .invalidTarget location => .invalidTarget (step :: location) }

def Targets.resolve
  (targets : Targets)
  (ty : DataType)
  (value : ⟦ty⟧)
  : TargetResolution :=
  match targets with
  | .global => .global
  | .fields locations nonempty =>
      match locations.find? (fun location => !Location.exists location ty value) with
      | some location => .invalidTarget location
      | none => .fields locations nonempty

def ValidationError.resolve
  (error : ValidationError)
  (ty : DataType)
  (value : ⟦ty⟧)
  : ResolvedError :=
  { message := error.message, targets := error.targets.resolve ty value }

def Checker.run {ty : DataType}
  (checker : Checker ty)
  (value : ⟦ty⟧)
  : List ResolvedError :=
  (checker.eval value).map fun error => error.resolve ty value

structure CheckedProperty (ty : DataType) where
  property : ⟦ty⟧ → Prop
  checker : Checker ty
  sound : ∀ value, (checker.run value).isEmpty = true → property value

def CheckedProperty.ofChecker {ty : DataType}
  (checker : Checker ty)
  : CheckedProperty ty :=
  { property := fun value => (checker.run value).isEmpty = true
    checker := checker
    sound := fun _ h => h }

abbrev CheckedProperty.ValidatedValue {ty : DataType}
  (checked : CheckedProperty ty)
  : Type :=
  { value : ⟦ty⟧ // checked.property value }

def CheckedProperty.validate {ty : DataType}
  (checked : CheckedProperty ty)
  (draft : ⟦ty⟧)
  : Option checked.ValidatedValue :=
  if h : (checked.checker.run draft).isEmpty = true then
    some { val := draft, property := checked.sound draft h }
  else none

abbrev Checker.ValidatedValue {ty : DataType} (checker : Checker ty) : Type :=
  (CheckedProperty.ofChecker checker).ValidatedValue

def Checker.validate {ty : DataType}
  (checker : Checker ty)
  (draft : ⟦ty⟧)
  : Option checker.ValidatedValue :=
  (CheckedProperty.ofChecker checker).validate draft

end Forms.Validation

namespace Forms

def Path.location {source target : DataType}
  (path : Path source target)
  : Validation.Location :=
  match path with
  | .self => []
  | .field (fieldNames := names) name rest => .field (names.label name) :: rest.location

def Path.locationExpr {source target input : DataType}
  (path : Path source target)
  : Validation.LocationExpr input :=
  path.location.map fun
    | .field name => .field name
    | .item index => .item (.value index)
    | .constructor tag => .constructor (.value tag)

end Forms
