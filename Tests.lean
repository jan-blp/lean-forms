import Forms.ExampleForms.Invoice
import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Person
import Forms.ExampleForms.Thermostat
import Forms.Runtime.Tui

open Forms Forms.Runtime

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def testRefinedTypes : IO Unit := do
  for temperature in [5, 22, 30] do
    check s!"TemperatureEndpoint {temperature}"
      ((ExampleForms.Thermostat.temperatureType.validate temperature).isSome)
  for draft in [![4, 18], ![31, 18], ![22, 4], ![30, 31]] do
    check "SharedTemperatureRuleAppliesToBothFields"
      ((ExampleForms.Thermostat.thermostatType.validate draft).isNone)
  check "BothLocalErrorsAndCrossFieldErrorAccumulate"
    ((ExampleForms.Thermostat.thermostatType.errors ![4, 31]).length == 3)
  for age in [18, 28, 120] do
    check s!"ValidAge {age}" ((ExampleForms.Person.ageType.validate age).map ExampleForms.Person.ageType.erase == some age)
  for age in [0, 17, 121, 999999999999999999999999] do
    check s!"InvalidAge {age}" ((ExampleForms.Person.ageType.validate age).isNone)
  check "TypedInitialErases" (JsonProtocol.valueToJson (ExampleForms.Thermostat.thermostatType.erase ExampleForms.Thermostat.initial) == Lean.Json.arr #[Lean.toJson "22", Lean.toJson "18"])
  check "CrossFieldRejectsInvalidDraft" ((ExampleForms.Thermostat.thermostatType.validate ![16, 18]).isNone)
  check "CrossFieldAllowsCorrection" ((ExampleForms.Thermostat.thermostatType.validate ![16, 16]).map (fun value => JsonProtocol.valueToJson (ExampleForms.Thermostat.thermostatType.erase value)) == some (Lean.Json.arr #[Lean.toJson "16", Lean.toJson "16"]))
  check "LocalAndParentErrorsAccumulate" ((ExampleForms.Thermostat.thermostatType.errors ![0, 18]).length == 2)
  let nested : RefinedDataType (.group ![.boolean, ExampleForms.Thermostat.shape]) :=
    .group fun
      | 0 => .base .boolean
      | 1 => ExampleForms.Thermostat.thermostatType
  let invalid : DataType.denote (.group ![.boolean, ExampleForms.Thermostat.shape])
    | 0 => true
    | 1 => ![16, 18]
  let valid : DataType.denote (.group ![.boolean, ExampleForms.Thermostat.shape])
    | 0 => true
    | 1 => ![16, 16]
  check "NestedRulesLiftBothPaths" ((nested.errors invalid).length == 1)
  check "NestedRulesPreserveValidation" ((nested.validate valid).map (fun value => JsonProtocol.valueToJson (nested.erase value)) == some (JsonProtocol.valueToJson valid))
  let some constraint := (nested.errors invalid)[0]?
    | throw (IO.userError "Expected away temperature error")
  check "ErrorLocationIsLifted" (match constraint.errorLocation with
    | some target => Path.toList target.path == [1, 1]
    | none => false)
  let atLeastTen : Constraint .natural :=
    { condition := .natLe (.value 10) (.project .here), errorMessage := "At least ten" }
  let atMostTwenty : Constraint .natural :=
    { condition := .natLe (.project .here) (.value 20), errorMessage := "At most twenty" }
  let stacked := RefinedDataType.refine (.refine (.base .natural) atLeastTen) atMostTwenty
  check "StackedRefinementsAccumulate"
    ((stacked.validate 9).isNone && (stacked.validate 21).isNone && (stacked.validate 15).isSome)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedBaseStillWorks" ((RefinedDataType.validate (.base .natural) huge).isSome)
  let invalidInitial := Path.set ExampleForms.Person.age 17 ExampleForms.Person.draft
  check "InitialDraftIsValidated" ((ExampleForms.Person.personType.errors invalidInitial).length == 1)
  check "RootDecodeCannotBypassAgeRule"
    (match JsonProtocol.decodeResult ExampleForms.Person.personType (JsonProtocol.valueToJson invalidInitial) with
      | .error _ => true
      | _ => false)

private def testHiddenValidation : IO Unit := do
  let hidden : Form ExampleForms.Thermostat.shape ExampleForms.Thermostat.shape :=
    .visibleWhen (.value false) ExampleForms.Thermostat.form
  let draft := ![16, 18]
  check "HiddenFieldsStillValidate"
    ((Form.fieldRefs hidden draft draft).isEmpty &&
      (ExampleForms.Thermostat.thermostatType.errors draft).length == 1 &&
      (ExampleForms.Thermostat.thermostatType.validate draft).isNone)

private def testPathsAndChoices : IO Unit := do
  let shown := Path.set ExampleForms.Person.subscribed true ExampleForms.Person.draft
  let fields := Form.fieldRefs ExampleForms.Person.form shown shown
  check "VisibilityStillWorks" ((Form.fieldRefs ExampleForms.Person.form ExampleForms.Person.draft ExampleForms.Person.draft).length == 4 && fields.length == 5)
  check "PathUpdatePreservesOtherValues" (JsonProtocol.valueToJson (Path.set ExampleForms.Person.age 42 shown) == Lean.Json.arr #[Lean.toJson "Ada", Lean.toJson "42", Lean.toJson true, Lean.Json.arr #[Lean.toJson "Lambda Lane", Lean.toJson (0 : Nat)]])
  check "LabelsFollowGroups"
    ((fields.map fun field => field.labels)[1]? == some ["Registration", "Age (18-120)"])
  for value in FinEnum.toList ExampleForms.Person.addressChoices.type do
    check "ChoiceRoundTrip"
      (JsonProtocol.valueFromJson (.choice ExampleForms.Person.addressChoices) (JsonProtocol.valueToJson (t := .choice ExampleForms.Person.addressChoices) value) == .ok value)
  check "ChoiceUsesLabels" (ExampleForms.Person.addressChoices.label .work == "Work")
  check "OutOfRangeJsonChoiceRejected"
    (match JsonProtocol.valueFromJson (.choice ExampleForms.Person.addressChoices) (Lean.toJson (3 : Nat)) with
      | .error _ => true
      | _ => false)

private instance : MonadTui (ReaderT String (Except IO.Error)) where
  runSpecification _ := read

private def testNativeBoundary : IO Unit := do
  let run := Tui.run (m := ReaderT String (Except IO.Error)) ExampleForms.Thermostat.thermostatType ExampleForms.Thermostat.form ExampleForms.Thermostat.draft
  check "LeanRejectsForgedNativeSuccess" (match run.run "[\"16\",\"18\"]" with
    | .error _ => true
    | _ => false)
  check "LeanConstructsProofForNativeResult" (match run.run "[\"16\",\"16\"]" with
    | .ok (some value) => JsonProtocol.valueToJson (ExampleForms.Thermostat.thermostatType.erase value) == Lean.Json.arr #[Lean.toJson "16", Lean.toJson "16"]
    | _ => false)
  check "NativeCancellationIsSeparate" (match run.run "null" with
    | .ok none => true
    | _ => false)
  check "MalformedNativeResultRejected" (match run.run "[\"16\"]" with
    | .error _ => true
    | _ => false)

private def testLists : IO Unit := do
  let refined := ExampleForms.Invoice.invoiceType
  let draft := ExampleForms.Invoice.draft
  let encoded := JsonProtocol.valueToJson draft
  check "ListRoundTrip" (match JsonProtocol.valueFromJson ExampleForms.Invoice.shape encoded with
    | .ok value => JsonProtocol.valueToJson value == encoded
    | _ => false)
  check "ListRefinementsRejectForgedResult" (match JsonProtocol.decodeResult refined
      (← IO.ofExcept (Lean.Json.parse "[[\"Bad\",\"0\",\"100\"]]")) with
    | .error _ => true
    | _ => false)
  check "EmptyListValidates" (match JsonProtocol.decodeResult refined (.arr #[]) with
    | .ok (some []) => true
    | _ => false)
  check "EveryItemValidated" (match JsonProtocol.decodeResult refined
      (← IO.ofExcept (Lean.Json.parse "[[\"Good\",\"1\",\"100\"],[\"Bad\",\"1\",\"0\"]]")) with
    | .error _ => true
    | _ => false)
  check "ListFieldIndices" ((ExampleForms.Invoice.form.fieldRefs draft draft).map (·.indices) == [[0,0], [0,1], [0,2]])
  check "ListRequiresArray" (match JsonProtocol.valueFromJson (.list .natural) (Lean.toJson "1") with
    | .error _ => true
    | _ => false)

private def testProtocol : IO Unit := do
  for (fixture, encoded) in [
      ("native/tui/tests/invoice.json", JsonProtocol.encode ExampleForms.Invoice.invoiceType ExampleForms.Invoice.form ExampleForms.Invoice.draft),
      ("native/tui/tests/person.json", JsonProtocol.encode ExampleForms.Person.personType ExampleForms.Person.form ExampleForms.Person.draft),
      ("native/tui/tests/thermostat.json", JsonProtocol.encode ExampleForms.Thermostat.thermostatType ExampleForms.Thermostat.form ExampleForms.Thermostat.draft)] do
    check "RustFixtureMatchesLean" ((← IO.FS.readFile fixture).trimAscii.toString == encoded)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedJsonRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (t := .natural) huge) == .ok huge)

def main : IO Unit := do
  testRefinedTypes
  testPathsAndChoices
  testHiddenValidation
  testNativeBoundary
  testProtocol
  testLists

section Theorems

example : ExampleForms.Invoice.invoiceType.denote = List ExampleForms.Invoice.itemType.denote := rfl

-- These equalities check the actual carriers, including nested local proofs.
example : ExampleForms.Person.ageType.denote = { n : Nat // (decide (18 ≤ n) && decide (n ≤ 120)) = true } := rfl
example : ExampleForms.Thermostat.thermostatType.denote =
    { p : (i : Fin 2) → { n : Nat // (decide (5 ≤ n) && decide (n ≤ 30)) = true } //
      decide ((p 1).val ≤ (p 0).val) = true } := rfl

end Theorems
