import Tests.Actions
import Tests.ComponentHistory
import Tests.Weakening
import Tests.Basket
import Tests.Composition
import Forms.ExampleForms.Booking
import Forms.ExampleForms.Location
import Forms.ExampleForms.Shapes
import Forms.ExampleForms.Invoice
import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Person
import Forms.ExampleForms.Thermostat
import Forms.Runtime.Tui

open Forms Forms.Composition Forms.Runtime

private def fieldRefs {state : DataType}
  (component : Component state)
  (value : ⟦state⟧) :=
  (FormSnapshot.render component value).fieldRefs

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def temperatures
  (home away : Nat)
  : ⟦ExampleForms.Thermostat.thermostat⟧
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

private def wrap {t : DataType} (enabled : Bool) (value : ⟦t⟧) : ⟦wrapper t⟧
  | .enabled => enabled
  | .content => value

private def refineWrapper {t : DataType}
  (refined : RefinedDataType t)
  : RefinedDataType (wrapper t) :=
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
  let nested : RefinedDataType (wrapper ExampleForms.Thermostat.thermostat) :=
    refineWrapper ExampleForms.Thermostat.thermostatType
  let invalid : ⟦wrapper ExampleForms.Thermostat.thermostat⟧ :=
    wrap true (temperatures 16 18)
  let valid : ⟦wrapper ExampleForms.Thermostat.thermostat⟧ :=
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
  let hidden : Component ExampleForms.Thermostat.thermostat :=
    .visibleWhen (.value false) ExampleForms.Thermostat.form
  let draft := (temperatures 16 18)
  check "HiddenFieldsStillValidate"
    ((fieldRefs hidden draft).isEmpty &&
      (RefinedDataType.errors ExampleForms.Thermostat.thermostatType draft).length == 1 &&
      (RefinedDataType.validate ExampleForms.Thermostat.thermostatType draft).isNone)

private def testPathsAndChoices : IO Unit := do
  let shown := Path.set ExampleForms.Person.subscribed true ExampleForms.Person.draft
  let fields := fieldRefs ExampleForms.Person.form shown
  let initialFields := fieldRefs ExampleForms.Person.form ExampleForms.Person.draft
  check "PostalMailShowsWholeAddress" (initialFields.length == 3 && fields.length == 5)
  check "PathUpdatePreservesOtherValues" (JsonProtocol.valueToJson (Path.set ExampleForms.Person.age 42 shown) == Lean.Json.mkObj [("name", Lean.toJson "Ada"), ("age", Lean.toJson "42"), ("subscribed", Lean.toJson true), ("address", Lean.Json.mkObj [("street", Lean.toJson "Lambda Lane"), ("kind", Lean.toJson (0 : Nat))])])
  check "LabelsFollowGroups"
    ((fields.map fun field => field.labels)[1]? == some ["Registration", "Age (18-120)"])
  for value in FinEnum.toList ExampleForms.Person.addressEnum do
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
    | .ok (some value) => JsonProtocol.valueToJson (RefinedDataType.erase ExampleForms.Thermostat.thermostatType value.value) == temperatureJson "16" "16"
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
  check "ListRoundTrip" (match JsonProtocol.valueFromJson ExampleForms.Invoice.invoice encoded with
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
  check "ListFieldIndices" ((fieldRefs ExampleForms.Invoice.form draft).map (·.indices) == [[0,0], [0,1], [0,2], [0], []])
  check "ListRequiresArray" (match JsonProtocol.valueFromJson (.list .natural) (Lean.toJson "1") with
    | .error _ => true
    | _ => false)

private def testSums : IO Unit := do
  let refined := ExampleForms.Shapes.shapeType
  let dot : ⟦ExampleForms.Shapes.shape⟧ := ⟨.dot, fun i => nomatch i⟩
  let valid : ⟦ExampleForms.Shapes.shape⟧ := ⟨.rectangle, fun | .width => 7 | .height => 2⟩
  let invalid : ⟦ExampleForms.Shapes.shape⟧ := ⟨.rectangle, fun | .width => 7 | .height => 0⟩
  let dimension : Expr ExampleForms.Shapes.shape .natural :=
    .cases (.project .self) fun
      | .dot => .value 0
      | .circle => .project .self
      | .rectangle => .project (.field .height .self)
  check "CasesReturnsSelectedPayloadValue" (Expr.eval dimension dot == 0 && Expr.eval dimension valid == 2)
  let name : Expr ExampleForms.Shapes.shape .text :=
    .cases (.project .self) fun
      | .dot => .value "Dot"
      | .circle => .value "Circle"
      | .rectangle => .value "Rectangle"
  check "CasesSupportsTextResult" (Expr.eval name dot == "Dot" && Expr.eval name valid == "Rectangle")
  let withinLimit : Expr ExampleForms.Shapes.shape .boolean := .natLe dimension (.value 1)
  check "CasesComposesWithExpressions" (Expr.eval withinLimit dot && !(Expr.eval withinLimit valid))
  let outer : DataType := wrapper ExampleForms.Shapes.shape
  let lifted : Expr outer .natural := Expr.weaken (.field .content .self) dimension
  check "CasesWeakensSubjectOnly" (Expr.eval lifted (wrap false valid) == 2)
  check "CasesEncodesResultType" (match (Expr.toJson dimension).getObjVal? "type" with
    | .ok ty => ty == DataType.toJson .natural
    | _ => false)

  for draft in [dot, valid, invalid] do
    let encoded := JsonProtocol.valueToJson draft
    check "SumDraftRoundTrip" (match JsonProtocol.valueFromJson ExampleForms.Shapes.shape encoded with
      | .ok value => JsonProtocol.valueToJson value == encoded
      | _ => false)
  check "InactiveConstructorDoesNotValidate" ((RefinedDataType.validate refined dot).isSome && (RefinedDataType.errors refined dot).isEmpty)
  check "SelectedConstructorConstructsProof" ((RefinedDataType.validate refined valid).isSome)
  check "SelectedConstructorRejectsInvalidDraft" ((RefinedDataType.validate refined invalid).isNone && (RefinedDataType.errors refined invalid).length == 1)
  check "SumProofErasesToOriginal" ((RefinedDataType.validate refined valid).map (fun v => JsonProtocol.valueToJson (RefinedDataType.erase refined v)) == some (JsonProtocol.valueToJson valid))
  check "SumOnlyShowsActivePayload" ((fieldRefs ExampleForms.Shapes.form dot).isEmpty &&
    (fieldRefs ExampleForms.Shapes.form valid).map (·.indices) == [[2,0], [2,1]])
  check "SumPayloadLabels" ((fieldRefs ExampleForms.Shapes.form valid).map (·.labels) ==
    [["Shape", "rectangle", "Dimensions", "Width"], ["Shape", "rectangle", "Dimensions", "Height"]])
  let nested : RefinedDataType (wrapper ExampleForms.Shapes.shape) := refineWrapper refined
  check "SumConstraintsWeakenThroughRecord" ((RefinedDataType.errors nested (wrap false invalid)).length == 1 &&
    (RefinedDataType.errors nested (wrap false dot)).isEmpty)
  let repeated := RefinedDataType.list refined
  check "SumConstraintsComposeWithLists" ((RefinedDataType.errors repeated [dot, valid]).isEmpty &&
    (RefinedDataType.errors repeated [dot, invalid]).length == 1 && (RefinedDataType.validate repeated [dot, invalid]).isNone)
  for malformed in ["{}", "[0,[]]", "{\"tag\":3,\"value\":[]}",
      "{\"tag\":-1,\"value\":[]}", "{\"tag\":\"0\",\"value\":[]}",
      "{\"tag\":\"dot\",\"value\":false}", "{\"tag\":\"circle\",\"value\":false}",
      "{\"tag\":\"dot\",\"value\":{},\"extra\":true}"] do
    check "MalformedSumRejected" (match JsonProtocol.valueFromJson ExampleForms.Shapes.shape
        (← IO.ofExcept (Lean.Json.parse malformed)) with
      | .error _ => true
      | _ => false)
  let run := Tui.run (m := ReaderT String (Except IO.Error)) refined ExampleForms.Shapes.form dot
  check "LeanRejectsForgedSumSuccess" (match run.run (JsonProtocol.valueToJson invalid).compress with
    | .error _ => true
    | _ => false)
  check "LeanAcceptsValidSumSubmission" (match run.run (JsonProtocol.valueToJson valid).compress with
    | .ok (some value) => JsonProtocol.valueToJson (RefinedDataType.erase refined value.value) == JsonProtocol.valueToJson valid
    | _ => false)
  check "SumCancellation" (match run.run "null" with
    | .ok none => true
    | _ => false)

private def testRecords : IO Unit := do
  let shape := ExampleForms.Thermostat.thermostat
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

private def testDisplayOrder : IO Unit := do
  let form : Component ExampleForms.Thermostat.thermostat :=
    (Component.Builder.group (fields := ExampleForms.Thermostat.temperatureFields) "Thermostat"
      (fun | .home => Component.Builder.field "Home" .naturalInput | .away => Component.Builder.field "Away" .naturalInput)
      (displayOrder := Equiv.swap .home .away)) .self
  let draft := ExampleForms.Thermostat.draft
  let fields := fieldRefs form draft
  check "DisplayOrderReordersFields" (fields.map (·.labels) == [["Thermostat", "Away"], ["Thermostat", "Home"]])
  check "DisplayOrderPreservesFieldIdentity" (fields.map (·.indices) == [[1], [0]])
  check "DisplayOrderEncodesPaths" (match (CompositionProtocol.componentToJson form).getObjVal? "children" with
    | .ok (.arr children) => ((children[0]!).getObjVal? "path").toOption == some (Lean.toJson (["away"] : List String))
    | _ => false)
  let hidden : Component ExampleForms.Thermostat.thermostat :=
    (Component.Builder.group (fields := ExampleForms.Thermostat.temperatureFields) "Thermostat"
      (fun
        | .home => Component.Builder.field "Home" .naturalInput
        | .away => Component.Builder.visibleWhen (.value false) (Component.Builder.field "Away" .naturalInput))
      (displayOrder := Equiv.swap .home .away)) .self
  check "DisplayOrderRespectsVisibility" ((fieldRefs hidden draft).map (·.indices) == [[0]])

private def testDisabled : IO Unit := do
  let form : Component .text := .disabledWhen (.value true) (.field .self "Name" .textInput)
  let enabled : Component .text := .disabledWhen (.value false) (.field .self "Name" .textInput)
  check "DisabledCondition" ((fieldRefs form "Ada").all (·.disabled))
  check "EnabledCondition" ((fieldRefs enabled "Ada").all (! ·.disabled))
  let nested := Component.disabledWhen (.value true) enabled
  check "ParentDisablesChildren" ((fieldRefs nested "Ada").all (·.disabled))
  check "DisabledStillVisible" ((fieldRefs nested "Ada").map (·.labels) == [["Name"]])
  let hidden := Component.visibleWhen (.value false) nested
  check "HiddenDisabledStaysHidden" ((fieldRefs hidden "Ada").isEmpty)
  check "DisabledJson" ((CompositionProtocol.componentToJson form).getObjValAs? String "kind" == .ok "disabledWhen")

private def testComputed : IO Unit := do
  let draft := ExampleForms.Invoice.draft
  let total := ExampleForms.Invoice.total
  check "InvoiceTotal" (Expr.eval total draft == 100)
  check "EmptyInvoiceTotal" (Expr.eval total [] == 0)
  let huge := 1234567890123456789012345678901234567890
  let item : ⟦ExampleForms.Invoice.item⟧ := fun
    | .description => "Large"
    | .quantity => huge
    | .unitPrice => huge
  check "UnboundedComputedTotal" (Expr.eval total [item, item] == 2 * huge * huge)
  let fields := fieldRefs ExampleForms.Invoice.form draft
  check "ComputedContent" (match fields.getLast? with
    | some field => match field.content with
      | .computed value => JsonProtocol.valueToJson value == Lean.toJson "100"
      | .input _ => false
    | none => false)
  let nestedShape : DataType := .record ExampleForms.Thermostat.temperatureFields fun _ => ExampleForms.Invoice.invoice
  let path : Path nestedShape ExampleForms.Invoice.invoice := .field .home .self
  let nested : ⟦nestedShape⟧ := fun _ => draft
  check "ComputedWeakening" (Expr.eval (Expr.weaken path total) nested == 100)

private def testDates : IO Unit := do
  let cases ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "native/tui/tests/dates.json"))
  let valid ← IO.ofExcept (cases.getObjValAs? (List String) "valid")
  let invalid ← IO.ofExcept (cases.getObjValAs? (List String) "invalid")
  for text in valid do
    let value ← IO.ofExcept (JsonProtocol.valueFromJson .date (Lean.toJson text))
    check "DateRoundTrip" (JsonProtocol.valueToJson (t := .date) value == Lean.toJson text)
  for text in invalid do
    check "RejectInvalidDate" (match JsonProtocol.valueFromJson .date (Lean.toJson text) with
      | .error _ => true
      | .ok _ => false)
  let early : Date := ⟨⟨2028, 2, 29, by decide⟩, by decide⟩
  let late : Date := ⟨⟨2028, 3, 1, by decide⟩, by decide⟩
  check "DateComparison" (Expr.eval (input := .date) (.dateLe (.value early) (.project .self)) late)
  check "DateComparisonEqual" (Expr.eval (input := .date) (.dateLe (.value early) (.project .self)) early)
  check "DateComparisonReversed" (!Expr.eval (input := .date) (.dateLe (.value late) (.project .self)) early)
  let range := RefinedDataType.dateRange early late
  for value in [early, late] do
    check "DateRangeIncludesEndpoints" ((RefinedDataType.validate range value).isSome)
  for value in ([⟨⟨2028, 2, 28, by decide⟩, by decide⟩,
                 ⟨⟨2028, 3, 2, by decide⟩, by decide⟩] : List Date) do
    check "DateRangeRejectsOutside" ((RefinedDataType.validate range value).isNone)
  check "DateRangeSingleDay" ((RefinedDataType.validate (.dateRange early early) early).isSome)
  check "DateRangeReversed" ((RefinedDataType.validate (.dateRange late early) early).isNone)
  let condition : Expr .date .boolean := .dateLe (.value early) (.project .self)
  check "DateComparisonWeakening" (Expr.eval (Expr.weaken ExampleForms.Booking.endDate condition) ExampleForms.Booking.draft)
  let invalidBooking := Path.set ExampleForms.Booking.endDate
    ⟨⟨2028, 2, 27, by decide⟩, by decide⟩ ExampleForms.Booking.draft
  check "DateRefinementRejectsForgedResult" (match JsonProtocol.decodeResult ExampleForms.Booking.bookingType
      (JsonProtocol.valueToJson invalidBooking) with
    | .error _ => true
    | _ => false)

private def testProtocol : IO Unit := do
  for (fixture, encoded) in [
      ("native/tui/tests/booking.json", CompositionProtocol.encode ExampleForms.Booking.bookingType ExampleForms.Booking.form ExampleForms.Booking.draft),
      ("native/tui/tests/location.json", CompositionProtocol.encode ExampleForms.Location.locationType ExampleForms.Location.form ExampleForms.Location.draft),
      ("native/tui/tests/shapes.json", CompositionProtocol.encode ExampleForms.Shapes.shapeType ExampleForms.Shapes.form ExampleForms.Shapes.draft),
      ("native/tui/tests/invoice.json", CompositionProtocol.encode ExampleForms.Invoice.invoiceType ExampleForms.Invoice.form ExampleForms.Invoice.draft),
      ("native/tui/tests/person.json", CompositionProtocol.encode ExampleForms.Person.personType ExampleForms.Person.form ExampleForms.Person.draft),
      ("native/tui/tests/thermostat.json", CompositionProtocol.encode ExampleForms.Thermostat.thermostatType ExampleForms.Thermostat.form ExampleForms.Thermostat.draft)] do
    check "RustFixtureMatchesLean" ((Lean.Json.parse (← IO.FS.readFile fixture)).toOption == (Lean.Json.parse encoded).toOption)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedJsonRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (t := .natural) huge) == .ok huge)

def main : IO Unit := do
  Tests.Actions.run
  Tests.ComponentHistory.run
  Tests.Weakening.run
  Tests.Basket.run
  Tests.Composition.run
  testRefinedTypes
  testPathsAndChoices
  testHiddenValidation
  testNativeBoundary
  testProtocol
  testLists
  testSums
  testRecords
  testDisplayOrder
  testDisabled
  testComputed
  testDates

section Theorems

example {tags : Enum} {constructors : tags → DataType}
    (branches : (i : tags) → RefinedDataType (constructors i)) :
    RefinedDataType.ValidatedValue (RefinedDataType.sum branches) = SumValue (fun i => RefinedDataType.ValidatedValue (branches i)) := rfl

example : RefinedDataType.ValidatedValue ExampleForms.Invoice.invoiceType = List (RefinedDataType.ValidatedValue ExampleForms.Invoice.itemType) := rfl

-- These equalities check the actual carriers, including nested local proofs.
example : RefinedDataType.ValidatedValue ExampleForms.Person.ageType = { n : Nat // (decide (18 ≤ n) && decide (n ≤ 120)) = true } := rfl
example : RefinedDataType.ValidatedValue ExampleForms.Thermostat.thermostatType =
    { p : (i : ExampleForms.Thermostat.TemperatureField) → { n : Nat // (decide (5 ≤ n) && decide (n ≤ 30)) = true } //
      decide ((p .away).val ≤ (p .home).val) = true } := rfl

end Theorems
