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
  .serverRefine inner (.require (fun n => n % 2 = 0)
    (fun n => s!"Server rule: {n} must be even.") (.fields [.self]))

example : (even (.base .natural)).ValidatedValue = { n : Nat // n % 2 = 0 } := rfl

def positive : RefinedDataType .natural :=
  .refine (.base .natural)
    (.require (fun n => 0 < n) (.not (.natLe (.project .self) (.value 0)))
      (.value "Must be positive") (.fields [.self]))

def run : IO Unit := do
  check "ServerPredicateAccepts" (((even positive).validate 2).map (even positive).erase == some 2)
  check "ServerPredicateRejects" (((even positive).validate 3).isNone)
  check "ServerKeepsInnerRefinement" (((even positive).validate 0).isNone)
  check "ServerLayerNotSerialized" ((even positive).toJson == positive.toJson)
  check "ServerOnlySerializesBase" ((even (.base .natural)).toJson == (RefinedDataType.base .natural).toJson)
  let stacked := (even (.base .natural)).serverRefine (.require (fun n => n < 3) (fun _ => "Below three") .global)
  check "ServerRulesAccumulate" ((stacked.errors 3).map (·.message) == ["Server rule: 3 must be even.", "Below three"])
  check "ServerRulesDisappearRecursively" (stacked.toJson == (RefinedDataType.base .natural).toJson)
  let shapes : RefinedDataType Shapes.shape := .sum fun
    | .dot => .record (fun i => nomatch i)
    | .circle => even (.base .natural)
    | .rectangle => .record (fun _ => even (.base .natural))
  let nested := RefinedDataType.list shapes
  let plain : RefinedDataType Shapes.shape := .sum fun
    | .dot => .record (fun i => nomatch i)
    | .circle => .base .natural
    | .rectangle => .record (fun _ => .base .natural)
  check "NestedServerRulesNotSerialized" (nested.toJson == (RefinedDataType.list plain).toJson)
  let rectangle : ⟦Shapes.shape⟧ := { tag := .rectangle, payload := fun | .width => 2 | .height => 3 }
  let expected : ResolvedError (.list Shapes.shape) :=
    ⟨"Server rule: 3 must be even.", .fields [.item 0 (.constructor .rectangle (.field .height .self))]⟩
  check "NestedServerErrorLocation" (Lean.toJson ((nested.errors [rectangle]).map ResolvedError.toJson) ==
    Lean.toJson [expected.toJson])
  check "NestedServerValidationRejects" ((nested.validate [rectangle]).isNone)

  -- The client receives no server rule, but replayed submissions still enforce it.
  let endpoint := Web.ComponentEndpoint.ofComponent (even (.base .natural)) Counter.form 0
  let client := Web.ComponentEndpoint.ofComponent (.base .natural) Counter.form 0
  check "ServerRuleAbsentFromFullSpecification" (endpoint.specification == client.specification)
  let odd ← IO.ofExcept (ComponentHistory.replay Counter.form 0 #[⟨.plusOne, ()⟩])
  check "ClientCanSubmitValueWithoutServerRule" ((client.submit (ComponentHistoryProtocol.encode odd)).isOk)
  check "ServerRejectsReplayedOddValue" (match endpoint.submit (ComponentHistoryProtocol.encode odd) with
    | .ok _ => false
    | .error error => error == (SubmissionProtocol.Error.invalidValue ((even (.base .natural)).errors 1)).toJson)
  let accepted ← IO.ofExcept (odd.apply ⟨.plusOne, ()⟩)
  check "ServerAcceptsReplayedEvenValue" ((endpoint.submit (ComponentHistoryProtocol.encode accepted)).isOk)
  IO.println "PASS: server-only refinements, nested locations, serialization omission, and submission enforcement"

end Tests.ServerRefinements
