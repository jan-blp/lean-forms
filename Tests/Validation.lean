import Tests.ValidationCheckers
import Forms.ExampleForms.Shapes
import Forms.Runtime.JsonProtocol

namespace Forms.Tests.ValidationExperiment

open Validation ExampleForms

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def item (description : String) (quantity : Nat) : ⟦Invoice.item⟧
  | .description => description
  | .quantity => quantity
  | .unitPrice => 100

private instance {α β : Type} [BEq α] [BEq β] : BEq (Except α β) where
  beq
    | .ok left, .ok right => left == right
    | .error left, .error right => left == right
    | .ok _, .error _ => false
    | .error _, .ok _ => false

private def locations
  (error : ResolvedError)
  : Except Location (Option (List Location)) :=
  match error.targets with
  | .global => .ok none
  | .fields paths _ => .ok (some paths)
  | .invalidTarget location => .error location

private def field (index : Nat) (name : String) : Location :=
  [.item index, .field name]

private def conservative : CheckedProperty .natural :=
  { property := fun n => 0 < n
    checker := .when (.not (.natLe (.value 2) (.project .self)))
      (.report (.value "At least two.") .global)
    sound := by
      intro n h
      simp [Checker.run, Checker.eval, Expr.eval, Path.get] at h
      have lower : 2 ≤ n := of_decide_eq_true h
      exact Nat.lt_of_lt_of_le (by decide : 0 < 2) lower }

example : conservative.ValidatedValue = { n : Nat // 0 < n } := rfl

private def conservativeType : RefinedDataType .natural :=
  .refine (.base .natural) conservative

example : conservativeType.ValidatedValue = { n : Nat // 0 < n } := rfl

def run : IO Unit := do
  let one : conservativeType.ValidatedValue := { val := 1, property := show 0 < (1 : Nat) from by decide }
  check "SoundCheckerMayRejectPropertyWitness"
    ((conservativeType.validate (conservativeType.erase one)).isNone)
  check "CheckedPropertyConstructsOrdinaryProof"
    ((conservative.validate 2).map (·.val) == some 2)
  check "RecursiveCheckedPropertyPreservesAcceptedValue"
    ((conservativeType.validate 2).map conservativeType.erase == some 2)
  check "OfCheckerKeepsOperationalGuarantee"
    (((CheckedProperty.ofChecker (.pass : Checker .natural)).validate 0).map (·.val) == some 0)
  let sameName : Expr .text .boolean := .textEq (.project .self) (.value "A")
  let lifted : Expr Invoice.item .boolean := sameName.weaken (.field .description .self)
  check "TextEqualityWeakensThroughRecord"
    (lifted.eval (item "A" 1) && !lifted.eval (item "B" 1))
  check "DynamicPassAcceptsValue"
    (((Checker.pass : Checker Invoice.invoice).validate [item "A" 0]).isSome)
  let checker := Forms.Tests.ValidationCheckers.checker
  for draft in [[], [item "A" 1], [item "A" 1, item "B" 2]] do
    check "DynamicAcceptsValidInvoice" ((checker.validate draft).isSome)
  for draft in [[item "A" 0], [item "A" 1, item "A" 1]] do
    check "DynamicRejectsInvalidInvoice" ((checker.validate draft).isNone)
  let errors := checker.run [item "A" 2, item "B" 0, item "A" 0]
  check "DynamicAccumulatesQuantityAndDuplicateErrors"
    (errors.map (·.message) == ["Quantity must be at least 1.", "Quantity must be at least 1.", "Duplicate item: A"])
  check "DynamicLocatesEachQuantityAndBothDuplicates"
    (errors.map locations == [
      .ok (some [field 1 "quantity"]),
      .ok (some [field 2 "quantity"]),
      .ok (some [field 0 "description", field 2 "description"])])
  check "DynamicReportsEachUnorderedPairOnce"
    ((checker.run [item "A" 1, item "A" 1, item "A" 1]).map locations == [
      .ok (some [field 0 "description", field 1 "description"]),
      .ok (some [field 0 "description", field 2 "description"]),
      .ok (some [field 1 "description", field 2 "description"])])
  check "DynamicValidationPreservesValue"
    ((checker.validate [item "A" 1]).map (fun value => Runtime.JsonProtocol.valueToJson value.val) ==
      some (Runtime.JsonProtocol.valueToJson (t := Invoice.invoice) [item "A" 1]))
  let bad : Checker Invoice.invoice :=
    .seq
      (.report (.value "Invalid index") (.fields [[.item (.value 9), .field "quantity"]]))
      (.report (.value "Unknown field") (.fields [[.item (.value 0), .field "missing"]]))
  let draft := [item "A" 1]
  check "DynamicInvalidLocationsAreExplicit"
    ((bad.run draft).map locations == [
      .error [.item 9, .field "quantity"],
      .error [.item 0, .field "missing"]])
  check "DynamicInvalidLocationsPreserveMessages"
    ((bad.run draft).map (·.message) == ["Invalid index", "Unknown field"])
  check "DynamicInvalidLocationsStillRejectValue" ((bad.validate draft).isNone)
  let mixed : Checker Invoice.invoice :=
    .report (.value "Mixed targets") (.fields [[.item (.value 0), .field "quantity"], [.item (.value 9), .field "quantity"]])
  check "DynamicMixedLocationsReportInvalidTarget"
    ((mixed.run draft).map locations == [.error [.item 9, .field "quantity"]])
  let multiple : Checker Invoice.invoice :=
    .report (.value "Multiple invalid targets") (.fields [[.item (.value 9)], [.item (.value 10)]])
  check "DynamicReportsFirstInvalidTarget"
    ((multiple.run draft).map locations == [.error [.item 9]])
  let root : Checker Invoice.invoice := .seq (.report (.value "Root") (.fields [[]])) (.report (.value "Global") .global)
  check "DynamicRootAndGlobalRemainDistinct"
    ((root.run draft).map locations == [.ok (some [[]]), .ok none])
  check "DynamicNestedListLocationExists"
    (Location.exists [.item 1, .item 0, .field "quantity"] (.list Invoice.invoice) [[], draft])
  check "DynamicNestedListIndexChecked"
    (!(Location.exists [.item 0, .item 0, .field "quantity"] (.list Invoice.invoice) [[], draft]))
  let rectangle : ⟦Shapes.shape⟧ :=
    { tag := .rectangle, payload := fun
        | .width => 2
        | .height => 0 }
  check "DynamicActiveConstructorLocationExists"
    (Location.exists [.constructor "rectangle", .field "height"] Shapes.shape rectangle)
  check "DynamicInactiveConstructorLocationRejected"
    (!(Location.exists [.constructor "circle", .field "height"] Shapes.shape rectangle))
  check "DynamicPayloadRequiresConstructorStep"
    (!(Location.exists [.field "value", .field "height"] Shapes.shape rectangle))
  check "DynamicFieldCannotStandForConstructor"
    (!(Location.exists [.field "rectangle", .field "height"] Shapes.shape rectangle))
  let wrongBranch : Validation.ValidationError :=
    { message := "Inactive payload", targets := .fields [[.constructor "circle"]] }
  check "DynamicInactiveConstructorErrorIsExplicit"
    (locations (wrongBranch.resolve Shapes.shape rectangle) == .error [.constructor "circle"])
  let nested : Checker (.list Shapes.shape) :=
    .report (.value "Invalid height") (.fields [[.item (.value 0), .constructor (.value "rectangle"), .field "height"]])
  check "DynamicListAndConstructorLocationPreserved"
    ((nested.run [rectangle]).map locations ==
      [.ok (some [[.item 0, .constructor "rectangle", .field "height"]])])
  check "DynamicCannotDescendIntoScalar"
    (!(Location.exists [.field "anything"] .natural 3))

end Forms.Tests.ValidationExperiment
