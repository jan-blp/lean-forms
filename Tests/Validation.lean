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

def targets {root : DataType} {value : ⟦root⟧} (error : CheckedError root value) : Lean.Json :=
  error.erase.targets.toJson

def fieldsAt {root : DataType} (locations : List (Location root))
    (nonempty : locations ≠ [] := by simp) : Lean.Json :=
  (TargetResolution.locations locations nonempty).toJson

def globalTarget : Lean.Json :=
  (TargetResolution.global (root := .natural)).toJson

def quantity (index : Nat) : Location Invoice.invoice :=
  .item index (.field .quantity .self)

def description (index : Nat) : Location Invoice.invoice :=
  .item index (.field .description .self)

def conservative : CheckedProperty .natural :=
  { property := fun n => 0 < n
    checker := fun n => if 2 ≤ n then [] else [{ message := "At least two.", targets := .global }]
    sound := by
      intro n h
      by_cases lower : 2 ≤ n
      · exact Nat.lt_of_lt_of_le (by decide : 0 < 2) lower
      · simp [lower] at h }

def conservativeType : RefinedDataType .natural :=
  .refine (.base .natural) conservative

example : conservativeType.ValidatedValue = { n : Nat // 0 < n } := rfl

def evenFirst : CheckedProperty (.list .natural) :=
  .require (fun values => values.headD 0 % 2 = 0) (fun _ => "First value must be even.")
    (fun values failed => .locations [.item ⟨0, by cases values <;> simp_all⟩ .self])

def run : IO Unit := do
  check "EmptyListNeedsNoErrorLocation" ((evenFirst.checker []).isEmpty)
  check "FailureProofConstructsValidHeadTarget"
    ((evenFirst.checker [3, 2]).map targets == [fieldsAt (root := .list .natural) [.item 0 .self]])
  let one : conservativeType.ValidatedValue := { val := 1, property := show 0 < (1 : Nat) from by decide }
  check "SoundCheckerMayRejectPropertyWitness"
    ((conservativeType.validate (conservativeType.erase one)).isNone)
  check "RecursiveCheckedPropertyPreservesAcceptedValue"
    ((conservativeType.validate 2).map conservativeType.erase == some 2)
  check "OfCheckerKeepsOperationalGuarantee"
    (((RefinedDataType.refine (.base .natural) (.ofChecker (fun _ => []))).validate 0).map (·.val) == some 0)
  let sameName : Expr .text .boolean := .textEq (.project .self) (.value "A")
  let lifted : Expr Invoice.item .boolean := sameName.weaken (.field .description .self)
  check "TextEqualityWeakensThroughRecord"
    (lifted.eval (item "A" 1) && !lifted.eval (item "B" 1))
  check "DynamicPassAcceptsValue"
    (((fun _ => []) : Checker Invoice.invoice) [item "A" 0]).isEmpty
  let checker := Forms.Tests.ValidationCheckers.checker
  for draft in [[], [item "A" 1], [item "A" 1, item "B" 2]] do
    check "DynamicAcceptsValidInvoice" ((checker draft).isEmpty)
  let errors := checker [item "A" 2, item "B" 0, item "A" 0]
  check "DynamicAccumulatesQuantityAndDuplicateErrors"
    (errors.map (·.message) == ["Quantity must be at least 1.", "Quantity must be at least 1.", "Duplicate item: A"])
  check "DynamicLocatesEachQuantityAndBothDuplicates"
    (errors.map targets == [
      fieldsAt [quantity 1],
      fieldsAt [quantity 2],
      fieldsAt [description 0, description 2]])
  check "DynamicReportsEachUnorderedPairOnce"
    ((checker [item "A" 1, item "A" 1, item "A" 1]).map targets == [
      fieldsAt [description 0, description 1],
      fieldsAt [description 0, description 2],
      fieldsAt [description 1, description 2]])
  check "DynamicValidationPreservesValue"
    (((RefinedDataType.refine (.base _) (.ofChecker checker)).validate [item "A" 1]).map (fun value => Runtime.JsonProtocol.valueToJson value.val) ==
      some (Runtime.JsonProtocol.valueToJson (t := Invoice.invoice) [item "A" 1]))
  let draft := [item "A" 1]
  let root : Checker Invoice.invoice := fun _ =>
    [{ message := "Root", targets := .locations [.self] }, { message := "Global", targets := .global }]
  check "RootAndGlobalRemainDistinct"
    ((root draft).map targets == [fieldsAt (root := Invoice.invoice) [.self], globalTarget])
  let nestedValue : ⟦.list Invoice.invoice⟧ := [[], draft]
  let quantityAt : ValidLocation (.list Invoice.invoice) nestedValue :=
    .item ⟨1, by decide⟩ (.item ⟨0, by decide⟩ (.field .quantity .self))
  check "NestedListLocationExists" (quantityAt.erase.exists nestedValue)
  let shapeChecker : Checker Shapes.shape := fun
    | ⟨.dot, _⟩ => []
    | ⟨.circle, radius⟩ => if radius > 0 then [] else
        [{ message := "Invalid radius", targets := .locations [.constructor .self] }]
    | ⟨.rectangle, sides⟩ => if sides .height > 0 then [] else
        [{ message := "Invalid height", targets := .locations [.constructor (.field .height .self)] }]
  let rectangle : ⟦Shapes.shape⟧ := ⟨.rectangle, fun | .width => 2 | .height => 0⟩
  let nested : Checker (.list Shapes.shape) := fun values =>
    (List.finRange values.length).flatMap fun index =>
      (shapeChecker values[index]).map (·.mapLocations (.item index))
  check "ActiveConstructorErrorLocation"
    ((shapeChecker rectangle).map targets == [fieldsAt (root := Shapes.shape) [.constructor .rectangle (.field .height .self)]])
  check "ListAndConstructorLocationPreserved"
    ((nested [rectangle]).map targets ==
      [fieldsAt (root := .list Shapes.shape) [.item 0 (.constructor .rectangle (.field .height .self))]])

example : True := by
  fail_if_success
    have invalid : CheckedError (.list .natural) [] :=
      { message := "Impossible", targets := .locations [.item ⟨0, by decide⟩ .self] }
  trivial

example : True := by
  fail_if_success
    have invalid : CheckedError Shapes.shape ⟨.circle, 2⟩ :=
      { message := "Wrong branch", targets := .locations [.constructor (.field .height .self)] }
  trivial

end Forms.Tests.ValidationExperiment
