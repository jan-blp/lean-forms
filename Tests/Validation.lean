module

public import Tests.ValidationCheckers
public import Forms.ExampleForms.Shapes
public import Forms.Runtime.JsonProtocol

@[expose] public section

namespace Forms.Tests.ValidationExperiment

open Validation ExampleForms

def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

def item (description : String) (quantity : Nat) : ⟦Invoice.item⟧
  | .description => description
  | .quantity => quantity
  | .unitPrice => 100

def targets {root : DataType} (error : ResolvedError root) : Lean.Json :=
  error.targets.toJson

def fieldsAt {root : DataType} (locations : List (Location root))
    (nonempty : locations ≠ [] := by simp) : Lean.Json :=
  (TargetResolution.locations locations nonempty).toJson

def invalidAt {root : DataType} (location : Location root) : Lean.Json :=
  (TargetResolution.invalidTarget location).toJson

def globalTarget : Lean.Json :=
  (TargetResolution.global (root := .natural)).toJson

def quantity (index : Nat) : Location Invoice.invoice :=
  .item index (.field .quantity .self)

def description (index : Nat) : Location Invoice.invoice :=
  .item index (.field .description .self)

def conservative : CheckedProperty .natural :=
  { property := fun n => 0 < n
    checker := .when (.not (.natLe (.value 2) (.project .self)))
      (.report (.value "At least two.") .global)
    sound := by
      intro n h
      simp [Checker.run, ScopedChecker.eval, ScopedChecker.when, Expr.eval, Path.get] at h
      have lower : 2 ≤ n := of_decide_eq_true h
      exact Nat.lt_of_lt_of_le (by decide : 0 < 2) lower }

def conservativeType : RefinedDataType .natural :=
  .refine (.base .natural) conservative

example : conservativeType.ValidatedValue = { n : Nat // 0 < n } := rfl

def run : IO Unit := do
  let one : conservativeType.ValidatedValue := { val := 1, property := show 0 < (1 : Nat) from by decide }
  check "SoundCheckerMayRejectPropertyWitness"
    ((conservativeType.validate (conservativeType.erase one)).isNone)
  check "RecursiveCheckedPropertyPreservesAcceptedValue"
    ((conservativeType.validate 2).map conservativeType.erase == some 2)
  check "OfCheckerKeepsOperationalGuarantee"
    (((RefinedDataType.refine (.base .natural) (.ofChecker .pass)).validate 0).map (·.val) == some 0)
  let sameName : Expr .text .boolean := .textEq (.project .self) (.value "A")
  let lifted : Expr Invoice.item .boolean := sameName.weaken (.field .description .self)
  check "TextEqualityWeakensThroughRecord"
    (lifted.eval (item "A" 1) && !lifted.eval (item "B" 1))
  check "DynamicPassAcceptsValue"
    ((Checker.run (ty := Invoice.invoice) .pass [item "A" 0]).isEmpty)
  let checker := Forms.Tests.ValidationCheckers.checker
  for draft in [[], [item "A" 1], [item "A" 1, item "B" 2]] do
    check "DynamicAcceptsValidInvoice" ((checker.run draft).isEmpty)
  let errors := checker.run [item "A" 2, item "B" 0, item "A" 0]
  check "DynamicAccumulatesQuantityAndDuplicateErrors"
    (errors.map (·.message) == ["Quantity must be at least 1.", "Quantity must be at least 1.", "Duplicate item: A"])
  check "DynamicLocatesEachQuantityAndBothDuplicates"
    (errors.map targets == [
      fieldsAt [quantity 1],
      fieldsAt [quantity 2],
      fieldsAt [description 0, description 2]])
  check "DynamicReportsEachUnorderedPairOnce"
    ((checker.run [item "A" 1, item "A" 1, item "A" 1]).map targets == [
      fieldsAt [description 0, description 1],
      fieldsAt [description 0, description 2],
      fieldsAt [description 1, description 2]])
  check "DynamicValidationPreservesValue"
    (((RefinedDataType.refine (.base _) (.ofChecker checker)).validate [item "A" 1]).map (fun value => Runtime.JsonProtocol.valueToJson value.val) ==
      some (Runtime.JsonProtocol.valueToJson (t := Invoice.invoice) [item "A" 1]))
  let bad : Checker Invoice.invoice :=
    .seq
      (.report (.value "Invalid index") (.locations [.item (.value 9) (.field .quantity .self)]))
      (.report (.value "Second invalid index") (.locations [.item (.value 1) .self]))
  let draft := [item "A" 1]
  check "DynamicInvalidLocationsAreExplicit"
    ((bad.run draft).map targets == [
      invalidAt (quantity 9),
      invalidAt (root := Invoice.invoice) (.item 1 .self)])
  check "DynamicInvalidLocationsPreserveMessages"
    ((bad.run draft).map (·.message) == ["Invalid index", "Second invalid index"])
  let mixed : Checker Invoice.invoice :=
    .report (.value "Mixed targets") (.locations [.item (.value 0) (.field .quantity .self), .item (.value 9) (.field .quantity .self)])
  check "DynamicMixedLocationsReportInvalidTarget"
    ((mixed.run draft).map targets == [invalidAt (quantity 9)])
  let multiple : Checker Invoice.invoice :=
    .report (.value "Multiple invalid targets") (.locations [.item (.value 9) .self, .item (.value 10) .self])
  check "DynamicReportsFirstInvalidTarget"
    ((multiple.run draft).map targets == [invalidAt (root := Invoice.invoice) (.item 9 .self)])
  let root : Checker Invoice.invoice :=
    .seq (.report (.value "Root") (.locations [.self])) (.report (.value "Global") .global)
  check "DynamicRootAndGlobalRemainDistinct"
    ((root.run draft).map targets == [fieldsAt (root := Invoice.invoice) [.self], globalTarget])
  let nestedValue : ⟦.list Invoice.invoice⟧ := [[], draft]
  let quantityAt (outer : Nat) : LocationExpr (.list Invoice.invoice) (.list Invoice.invoice) :=
    .item (.value outer) (.item (.value 0) (.field .quantity .self))
  check "DynamicNestedListLocationExists" (((quantityAt 1).eval nestedValue).exists nestedValue)
  check "DynamicNestedListIndexChecked" (!((quantityAt 0).eval nestedValue).exists nestedValue)
  let rectangle : ⟦Shapes.shape⟧ :=
    { tag := .rectangle, payload := fun
        | .width => 2
        | .height => 0 }
  let height : LocationExpr Shapes.shape Shapes.shape := .constructor .rectangle (.field .height .self)
  check "DynamicActiveConstructorLocationExists" ((height.eval rectangle).exists rectangle)
  let circle : Shapes.shape.denote := { tag := .circle, payload := 1 }
  check "DynamicInactiveConstructorLocationRejected" (!(height.eval circle).exists circle)
  let wrongBranch : Checker Shapes.shape :=
    .report (.value "Inactive payload") (.locations [.constructor .circle .self])
  check "DynamicInactiveConstructorErrorIsExplicit"
    ((wrongBranch.run rectangle).map targets == [invalidAt (root := Shapes.shape) (.constructor .circle .self)])
  let nested : Checker (.list Shapes.shape) :=
    .report (.value "Invalid height") (.locations [.item (.value 0) (.constructor .rectangle (.field .height .self))])
  check "DynamicListAndConstructorLocationPreserved"
    ((nested.run [rectangle]).map targets ==
      [fieldsAt (root := .list Shapes.shape) [.item 0 (.constructor .rectangle (.field .height .self))]])

end Forms.Tests.ValidationExperiment
