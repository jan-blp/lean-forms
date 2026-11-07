module

public import Forms.Core.RefinedDataType.Theorems
public import Forms.Runtime.Web
public import Forms.ExampleForms.Counter
public import Forms.ExampleForms.Shapes

@[expose] public section

namespace Tests.ServerRefinements
open Forms Forms.Validation Forms.Runtime Forms.ExampleForms Forms.Composition

def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

def even (inner : RefinedDataType .natural := .base .natural) : RefinedDataType .natural :=
  .serverRefine inner {
    property := fun n => n % 2 = 0
    check := fun n =>
      if h : n % 2 = 0 then .valid h
      else .invalid h s!"Server rule: {n} must be even." (.locations [.self]) }

example : (even (.base .natural)).ValidatedValue = { n : Nat // n % 2 = 0 } := rfl

def positive : RefinedDataType .natural :=
  .refine (.base .natural)
    (.require (fun n => 0 < n) (fun _ => "Must be positive") (fun _ _ => .locations [.self]))

-- Failure proves that the list has a first element; no fallback target is needed.
def evenFirst : RefinedDataType (.list .natural) :=
  .serverRefine (.base _) {
    property := fun values => values.headD 0 % 2 = 0
    check := fun values =>
      if h : values.headD 0 % 2 = 0 then .valid h
      else .invalid h "First value must be even."
        (.locations [.item ⟨0, by cases values <;> simp_all⟩ .self]) }

-- The payload type follows the active constructor, without a tag argument.
def evenShape : RefinedDataType Shapes.shape :=
  .serverRefine (.base _) {
    property := fun value => match value with
      | ⟨.dot, _⟩ => True
      | ⟨.circle, radius⟩ => radius % 2 = 0
      | ⟨.rectangle, sides⟩ => sides .height % 2 = 0
    check := fun
      | ⟨.dot, _⟩ => .valid trivial
      | ⟨.circle, radius⟩ =>
        if h : radius % 2 = 0 then .valid h
        else .invalid h "Size must be even." (.locations [.constructor .self])
      | ⟨.rectangle, sides⟩ =>
        if h : sides .height % 2 = 0 then .valid h
        else .invalid h "Size must be even." (.locations [.constructor (.field .height .self)]) }

example : True := by
  fail_if_success
    have invalid : ValidLocation (.list .natural) [] := .item ⟨0, by decide⟩ .self
  trivial

example : True := by
  fail_if_success
    have invalid : ValidLocation Shapes.shape ⟨.circle, 2⟩ :=
      .constructor (.field .width .self)
  trivial

example {t : DataType} (checked : ServerProperty t) (value : ⟦t⟧) :
    checked.errors value = [] ↔ checked.property value := by
  cases decision : checked.check value <;> simp_all [ServerProperty.errors]

def run : IO Unit := do
  check "EmptyServerListAccepted" ((evenFirst.validate []).isSome)
  check "EvenFirstServerListAccepted" ((evenFirst.validate [2, 3]).isSome)
  check "OddFirstServerListRejected" ((evenFirst.validate [3, 2]).isNone)
  check "DependentServerListTarget" ((evenFirst.errors [3, 2]).map (·.toJson) ==
    [({ message := "First value must be even.", targets := .locations [.item 0 .self] }
      : ResolvedError (.list .natural)).toJson])
  check "DependentServerCircleTarget" ((evenShape.errors ⟨.circle, 3⟩).map (·.toJson) ==
    [({ message := "Size must be even.", targets := .locations [.constructor .circle .self] }
      : ResolvedError Shapes.shape).toJson])
  check "DependentServerRectangleTarget" (
    (evenShape.errors ⟨.rectangle, fun | .width => 2 | .height => 3⟩).map (·.toJson) ==
    [({ message := "Size must be even.", targets := .locations [.constructor .rectangle (.field .height .self)] }
      : ResolvedError Shapes.shape).toJson])

  check "ServerPredicateAccepts" (((even positive).validate 2).map (even positive).erase == some 2)
  check "ServerPredicateRejects" (((even positive).validate 3).isNone)
  check "ServerKeepsInnerRefinement" (((even positive).validate 0).isNone)
  let stacked := (even (.base .natural)).serverRefine {
    property := fun n => n < 3
    check := fun n => if h : n < 3 then .valid h else .invalid h "Below three" .global }
  check "ServerRulesAccumulate" ((stacked.errors 3).map (·.message) == ["Server rule: 3 must be even.", "Below three"])
  let shapes : RefinedDataType Shapes.shape := .sum fun
    | .dot => .record (fun i => nomatch i)
    | .circle => even (.base .natural)
    | .rectangle => .record (fun _ => even (.base .natural))
  let nested := RefinedDataType.list shapes
  let rectangle : ⟦Shapes.shape⟧ := { tag := .rectangle, payload := fun | .width => 2 | .height => 3 }
  let expected : ResolvedError (.list Shapes.shape) :=
    ⟨"Server rule: 3 must be even.", .locations [.item 0 (.constructor .rectangle (.field .height .self))]⟩
  check "NestedServerErrorLocation" (Lean.toJson ((nested.errors [rectangle]).map ResolvedError.toJson) ==
    Lean.toJson [expected.toJson])
  check "NestedServerValidationRejects" ((nested.validate [rectangle]).isNone)

  -- The client receives no server rule, but replayed submissions still enforce it.
  let endpoint := Web.ComponentEndpoint.ofComponent (even (.base .natural)) Counter.form 0
  let client := Web.ComponentEndpoint.ofComponent (.base .natural) Counter.form 0
  let odd ← IO.ofExcept (ComponentHistory.replay Counter.form 0 #[⟨.plusOne, ()⟩])
  check "ClientCanSubmitValueWithoutServerRule" ((client.submit (ComponentHistoryProtocol.encode odd)).isOk)
  check "ServerRejectsReplayedOddValue" (match endpoint.submit (ComponentHistoryProtocol.encode odd) with
    | .ok _ => false
    | .error error => error == (SubmissionProtocol.Error.invalidValue ((even (.base .natural)).errors 1)).toJson)
  let accepted ← IO.ofExcept (odd.apply ⟨.plusOne, ()⟩)
  check "ServerAcceptsReplayedEvenValue" ((endpoint.submit (ComponentHistoryProtocol.encode accepted)).isOk)
  IO.println "PASS: server-only refinements, nested locations, serialization omission, and submission enforcement"

end Tests.ServerRefinements
