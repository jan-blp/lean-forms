import Forms.ExampleForms.Invoice
import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Person
import Forms.ExampleForms.Thermostat
import Forms.Runtime.Tui

open Forms Forms.Runtime

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def temperatures (home away : Nat) : DataType.denote ExampleForms.Thermostat.shape
  | .home => home
  | .away => away

private def temperatureJson (home away : String) : Lean.Json :=
  .mkObj [("home", Lean.toJson home), ("away", Lean.toJson away)]

private inductive WrapperField where
  | enabled | content
  deriving DecidableEq

private instance : FinEnum WrapperField :=
  FinEnum.ofList [.enabled, .content] (by grind [WrapperField])

private def wrapperFields : Enum where
  type := WrapperField
  label | .enabled => "enabled" | .content => "content"

private abbrev wrapper (t : DataType) : DataType := .record wrapperFields fun
  | .enabled => .boolean
  | .content => t

private def wrap {t : DataType} (enabled : Bool) (value : DataType.denote t) : DataType.denote (wrapper t)
  | .enabled => enabled
  | .content => value

private def refineWrapper {t : DataType} (refined : RefinedDataType t) : RefinedDataType (wrapper t) :=
  .record fun | .enabled => .base .boolean | .content => refined

private def testRefinedTypes : IO Unit := do
  for temperature in [5, 22, 30] do
    check s!"TemperatureEndpoint {temperature}"
      ((RefinedDataType.validate ExampleForms.Thermostat.temperatureType temperature).isSome)
  for draft in [(temperatures 4 18), (temperatures 31 18), (temperatures 22 4), (temperatures 30 31)] do
    check "SharedTemperatureRuleAppliesToBothFields"
      ((RefinedDataType.validate ExampleForms.Thermostat.thermostatType draft).isNone)
  check "BothLocalErrorsAndCrossFieldErrorAccumulate"
    ((RefinedDataType.errors ExampleForms.Thermostat.thermostatType (temperatures 4 31)).length == 3)
  for age in [18, 28, 120] do
    check s!"ValidAge {age}" ((RefinedDataType.validate ExampleForms.Person.ageType age).map (RefinedDataType.erase ExampleForms.Person.ageType) == some age)
  for age in [0, 17, 121, 999999999999999999999999] do
    check s!"InvalidAge {age}" ((RefinedDataType.validate ExampleForms.Person.ageType age).isNone)
  check "TypedInitialErases" (JsonProtocol.valueToJson (RefinedDataType.erase ExampleForms.Thermostat.thermostatType ExampleForms.Thermostat.initial) == temperatureJson "22" "18")
  check "CrossFieldRejectsInvalidDraft" ((RefinedDataType.validate ExampleForms.Thermostat.thermostatType (temperatures 16 18)).isNone)
  check "CrossFieldAllowsCorrection" ((RefinedDataType.validate ExampleForms.Thermostat.thermostatType (temperatures 16 16)).map (fun value => JsonProtocol.valueToJson (RefinedDataType.erase ExampleForms.Thermostat.thermostatType value)) == some (temperatureJson "16" "16"))
  check "LocalAndParentErrorsAccumulate" ((RefinedDataType.errors ExampleForms.Thermostat.thermostatType (temperatures 0 18)).length == 2)
  let nested : RefinedDataType (wrapper ExampleForms.Thermostat.shape) :=
    refineWrapper ExampleForms.Thermostat.thermostatType
  let invalid : DataType.denote (wrapper ExampleForms.Thermostat.shape) :=
    wrap true (temperatures 16 18)
  let valid : DataType.denote (wrapper ExampleForms.Thermostat.shape) :=
    wrap true (temperatures 16 16)
  check "NestedRulesLiftBothPaths" ((RefinedDataType.errors nested invalid).length == 1)
  check "NestedRulesPreserveValidation" ((RefinedDataType.validate nested valid).map (fun value => JsonProtocol.valueToJson (RefinedDataType.erase nested value)) == some (JsonProtocol.valueToJson valid))
  let some constraint := (RefinedDataType.errors nested invalid)[0]?
    | throw (IO.userError "Expected away temperature error")
  check "ErrorLocationIsLifted" (match constraint.errorLocation with
    | some target => Path.toList target.path == ["content", "away"]
    | none => false)
  let atLeastTen : Constraint .natural :=
    { condition := .natLe (.value 10) (.project .self), errorMessage := "At least ten" }
  let atMostTwenty : Constraint .natural :=
    { condition := .natLe (.project .self) (.value 20), errorMessage := "At most twenty" }
  let stacked := RefinedDataType.refine (.refine (.base .natural) atLeastTen) atMostTwenty
  check "StackedRefinementsAccumulate"
    ((RefinedDataType.validate stacked 9).isNone && (RefinedDataType.validate stacked 21).isNone && (RefinedDataType.validate stacked 15).isSome)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedBaseStillWorks" ((RefinedDataType.validate (.base .natural) huge).isSome)
  let invalidInitial := Path.set ExampleForms.Person.age 17 ExampleForms.Person.draft
  check "InitialDraftIsValidated" ((RefinedDataType.errors ExampleForms.Person.personType invalidInitial).length == 1)
  check "RootDecodeCannotBypassAgeRule"
    (match JsonProtocol.decodeResult ExampleForms.Person.personType (JsonProtocol.valueToJson invalidInitial) with
      | .error _ => true
      | _ => false)

private def testHiddenValidation : IO Unit := do
  let hidden : Form ExampleForms.Thermostat.shape ExampleForms.Thermostat.shape :=
    .visibleWhen (.value false) ExampleForms.Thermostat.form
  let draft := (temperatures 16 18)
  check "HiddenFieldsStillValidate"
    ((Form.fieldRefs hidden draft draft).isEmpty &&
      (RefinedDataType.errors ExampleForms.Thermostat.thermostatType draft).length == 1 &&
      (RefinedDataType.validate ExampleForms.Thermostat.thermostatType draft).isNone)

private def testPathsAndChoices : IO Unit := do
  let shown := Path.set ExampleForms.Person.subscribed true ExampleForms.Person.draft
  let fields := Form.fieldRefs ExampleForms.Person.form shown shown
  check "VisibilityStillWorks" ((Form.fieldRefs ExampleForms.Person.form ExampleForms.Person.draft ExampleForms.Person.draft).length == 4 && fields.length == 5)
  check "PathUpdatePreservesOtherValues" (JsonProtocol.valueToJson (Path.set ExampleForms.Person.age 42 shown) == Lean.Json.mkObj [("name", Lean.toJson "Ada"), ("age", Lean.toJson "42"), ("subscribed", Lean.toJson true), ("address", Lean.Json.mkObj [("street", Lean.toJson "Lambda Lane"), ("kind", Lean.toJson (0 : Nat))])])
  check "LabelsFollowGroups"
    ((fields.map fun field => field.labels)[1]? == some ["Registration", "Age (18-120)"])
  for value in FinEnum.toList ExampleForms.Person.addressEnum.type do
    check "ChoiceRoundTrip"
      (JsonProtocol.valueFromJson (.enum ExampleForms.Person.addressEnum) (JsonProtocol.valueToJson (t := .enum ExampleForms.Person.addressEnum) value) == .ok value)
  check "ChoiceUsesLabels" (ExampleForms.Person.addressEnum.label .work == "Work")
  check "OutOfRangeJsonChoiceRejected"
    (match JsonProtocol.valueFromJson (.enum ExampleForms.Person.addressEnum) (Lean.toJson (3 : Nat)) with
      | .error _ => true
      | _ => false)

private instance : MonadTui (ReaderT String (Except IO.Error)) where
  runSpecification _ := read

private def testNativeBoundary : IO Unit := do
  let run := Tui.run (m := ReaderT String (Except IO.Error)) ExampleForms.Thermostat.thermostatType ExampleForms.Thermostat.form ExampleForms.Thermostat.draft
  check "LeanRejectsForgedNativeSuccess" (match run.run "{\"home\":\"16\",\"away\":\"18\"}" with
    | .error _ => true
    | _ => false)
  check "LeanConstructsProofForNativeResult" (match run.run "{\"home\":\"16\",\"away\":\"16\"}" with
    | .ok (some value) => JsonProtocol.valueToJson (RefinedDataType.erase ExampleForms.Thermostat.thermostatType value) == temperatureJson "16" "16"
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
      (← IO.ofExcept (Lean.Json.parse "[{\"description\":\"Bad\",\"quantity\":\"0\",\"unitPrice\":\"100\"}]")) with
    | .error _ => true
    | _ => false)
  check "EmptyListValidates" (match JsonProtocol.decodeResult refined (.arr #[]) with
    | .ok (some []) => true
    | _ => false)
  check "EveryItemValidated" (match JsonProtocol.decodeResult refined
      (← IO.ofExcept (Lean.Json.parse "[{\"description\":\"Good\",\"quantity\":\"1\",\"unitPrice\":\"100\"},{\"description\":\"Bad\",\"quantity\":\"1\",\"unitPrice\":\"0\"}]")) with
    | .error _ => true
    | _ => false)
  check "ListFieldIndices" ((Form.fieldRefs ExampleForms.Invoice.form draft draft).map (·.indices) == [[0,0], [0,1], [0,2]])
  check "ListRequiresArray" (match JsonProtocol.valueFromJson (.list .natural) (Lean.toJson "1") with
    | .error _ => true
    | _ => false)

private def testRecords : IO Unit := do
  let shape := ExampleForms.Thermostat.shape
  for malformed in ["{}", "[]", "{\"home\":\"22\"}",
      "{\"home\":\"22\",\"wrong\":\"18\"}",
      "{\"home\":\"22\",\"away\":\"18\",\"extra\":true}",
      "{\"home\":true,\"away\":\"18\"}"] do
    check "MalformedRecordRejected" (match JsonProtocol.valueFromJson shape
        (← IO.ofExcept (Lean.Json.parse malformed)) with
      | .error _ => true
      | _ => false)
  let reordered ← IO.ofExcept (Lean.Json.parse "{\"away\":\"18\",\"home\":\"22\"}")
  check "RecordFieldsDecodeByName" (match JsonProtocol.valueFromJson shape reordered with
    | .ok value => value .home == 22 && value .away == 18
    | _ => false)
  check "PathsEncodeFieldNames" (Path.toList ExampleForms.Person.street == ["address", "street"])

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
  testRecords

section Theorems

example : RefinedDataType.ValidatedValue ExampleForms.Invoice.invoiceType = List (RefinedDataType.ValidatedValue ExampleForms.Invoice.itemType) := rfl

-- These equalities check the actual carriers, including nested local proofs.
example : RefinedDataType.ValidatedValue ExampleForms.Person.ageType = { n : Nat // (decide (18 ≤ n) && decide (n ≤ 120)) = true } := rfl
example : RefinedDataType.ValidatedValue ExampleForms.Thermostat.thermostatType =
    { p : (i : ExampleForms.Thermostat.TemperatureField) → { n : Nat // (decide (5 ≤ n) && decide (n ≤ 30)) = true } //
      decide ((p .away).val ≤ (p .home).val) = true } := rfl

end Theorems
