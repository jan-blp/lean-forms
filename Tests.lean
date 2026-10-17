import Forms.Runtime.FormSnapshot
import Forms.ExampleForms.Shapes
import Forms.ExampleForms.Location
import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Person
import Forms.Runtime.Tui

open Forms Forms.Composition Forms.Runtime

private def fieldRefs {state : DataType} (component : Component state) (value : ⟦state⟧) :=
  (FormSnapshot.render component value).fieldRefs

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def testEditsAndVisibility : IO Unit := do
  let initial := ExampleForms.Person.initial
  let form := ExampleForms.Person.form
  check "InitiallyVisibleFields" ((fieldRefs form initial).length == 2)
  let visible := Path.set ExampleForms.Person.subscribed true initial
  check "PostalMailShowsAddress" ((fieldRefs form visible).length == 5)
  let changed := Path.set ExampleForms.Person.number 42 visible
  check "NestedEditPreservesOtherFields" (JsonProtocol.valueToJson changed == Lean.Json.mkObj [("name", Lean.toJson "Ada"), ("subscribed", Lean.toJson true),
      ("address", Lean.Json.mkObj [("street", Lean.toJson "Lambda Lane"), ("number", Lean.toJson "42"), ("kind", Lean.toJson (0 : Nat))])])
  let hidden := Path.set ExampleForms.Person.subscribed false changed
  check "HidingPreservesNestedValue"
    ((fieldRefs form hidden).length == 2 && Path.get ExampleForms.Person.number hidden == 42)
  check "ShowingRestoresEditedAddress"
    (JsonProtocol.valueToJson (Path.set ExampleForms.Person.subscribed true hidden) == JsonProtocol.valueToJson changed)

private def testLabeledFields : IO Unit := do
  let value := Path.set ExampleForms.Person.subscribed true ExampleForms.Person.initial
  let fields := fieldRefs ExampleForms.Person.form value
  check "GeneratedLabelsFollowGroups"
    (List.map (fun field => field.labels) fields ==
      [["Person", "Name"], ["Person", "Send me postal mail"],
       ["Person", "Address", "Street"],
       ["Person", "Address", "Number"],
       ["Person", "Address", "Kind"]])
  check "GeneratedFieldIndices"
    (fields.map (·.indices) == [[0], [1], [2, 0], [2, 1], [2, 2]])

private def testPredicates : IO Unit := do
  let eligible : Expr ExampleForms.Person.person .boolean :=
    .and (.value true)
      (.natLe (.value 10) (.project ExampleForms.Person.number))
  check "EvaluatesTypedPredicate" (Expr.eval eligible ExampleForms.Person.initial)
  check "PredicateUsesEditedValue"
    (!(Expr.eval eligible (Path.set ExampleForms.Person.number 9 ExampleForms.Person.initial)))

private def testChoice : IO Unit := do
  let domain := ExampleForms.Person.addressEnum
  for value in FinEnum.toList domain do
    check "ChoiceRoundTripPreservesEnumValue"
      (JsonProtocol.valueFromJson (.enum domain)
        (JsonProtocol.valueToJson (t := .enum domain) value) == .ok value)
  check "ChoiceDisplaysEnumLabel" (domain.label .work == "Work")
  for json in [Lean.toJson (3 : Nat), Lean.toJson (-1 : Int), Lean.toJson "1", Lean.Json.null] do
    check "RejectsInvalidChoiceResult"
      (match JsonProtocol.valueFromJson (.enum domain) json with
        | .error _ => true
        | .ok _ => false)

private def testGroups : IO Unit := do
  let empty : DataType := .record ⟨Empty, Empty.elim, by intro i; exact Empty.elim i⟩ (fun i => nomatch i)
  let emptyValue ← IO.ofExcept (JsonProtocol.valueFromJson empty (.mkObj []))
  check "EmptyGroupRoundTrip" (JsonProtocol.valueToJson emptyValue == .mkObj [])
  let singleton : DataType := .record ⟨Unit, fun _ => "only", by intro a b _; cases a; cases b; rfl⟩ (fun _ => .text)
  let singleValue ← IO.ofExcept (JsonProtocol.valueFromJson singleton (.mkObj [("only", Lean.toJson "only")]))
  check "SingleChildGroupRoundTrip" (JsonProtocol.valueToJson singleValue == .mkObj [("only", Lean.toJson "only")])
  for json in [Lean.Json.arr #[], .arr #[Lean.toJson "one", Lean.toJson "two"],
      .arr #[Lean.toJson true]] do
    check "RejectsWrongGroupLengthOrChildType"
      (match JsonProtocol.valueFromJson singleton json with
      | .error _ => true
      | .ok _ => false)
  let addressPath : Path ExampleForms.Person.person ExampleForms.Person.address := .field .address .self
  let numberPath : Path ExampleForms.Person.address .natural := .field .number .self
  check "ComposedGroupPath"
    ((addressPath.trans numberPath).toList == ["address", "number"] &&
      (addressPath.trans numberPath).get ExampleForms.Person.initial == 12)

private def testLists : IO Unit := do
  let initial := ExampleForms.Invoice.initial
  check "ListRoundTrip"
    (match JsonProtocol.valueFromJson ExampleForms.Invoice.invoice (JsonProtocol.valueToJson initial) with
    | .ok value => JsonProtocol.valueToJson value == JsonProtocol.valueToJson initial
    | .error _ => false)
  check "ListFieldIndices"
    ((fieldRefs ExampleForms.Invoice.form initial).map (·.indices) == [[0, 0], [0, 1], [0, 2]])
  check "EmptyListRoundTrip"
    (JsonProtocol.valueFromJson (.list .natural) (.arr #[]) == .ok [])
  check "ListRequiresArray"
    (match JsonProtocol.valueFromJson (.list .natural) (Lean.toJson "bad") with
    | .error _ => true
    | .ok _ => false)
  let allPositive : Expr (.list .natural) .boolean :=
    .all (.project .self) (.natLe (.value 1) (.project .self))
  check "AllListItems" (allPositive.eval [1, 2] && !(allPositive.eval [1, 0]))
  let fixture ← IO.FS.readFile "native/tui/tests/invoice.json"
  check "InvoiceFixtureMatchesLean"
    ((← IO.ofExcept (Lean.Json.parse fixture)).compress == JsonProtocol.encode ExampleForms.Invoice.form initial)

private def testDates : IO Unit := do
  let cases ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "native/tui/tests/dates.json"))
  let valid ← IO.ofExcept (cases.getObjValAs? (List String) "valid")
  let invalid ← IO.ofExcept (cases.getObjValAs? (List String) "invalid")
  for text in valid do
    check "DateRoundTrip" ((Date.ofString? text).map Date.toString == some text)
  for text in invalid do
    check "RejectInvalidDate" ((Date.ofString? text).isNone)
  let early : Date := ⟨⟨2028, 2, 29, by decide⟩, by decide⟩
  let late : Date := ⟨⟨2028, 3, 1, by decide⟩, by decide⟩
  check "DateComparison" (Expr.eval (input := .date) (.dateLe (.value early) (.project .self)) late)
  check "DateComparisonEqual" (Expr.eval (input := .date) (.dateLe (.value early) (.project .self)) early)
  check "DateComparisonReversed" (!Expr.eval (input := .date) (.dateLe (.value late) (.project .self)) early)

private def testSums : IO Unit := do
  for (fixture, encoded) in [
      ("native/tui/tests/shapes.json", JsonProtocol.encode ExampleForms.Shapes.form ExampleForms.Shapes.initial),
      ("native/tui/tests/location.json", JsonProtocol.encode ExampleForms.Location.form ExampleForms.Location.initial)] do
    let fixtureJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile fixture))
    let encodedJson ← IO.ofExcept (Lean.Json.parse encoded)
    check "SumFixtureMatchesLean" (fixtureJson.compress == encodedJson.compress)
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
  check "CasesEncodesResultType" (match (Expr.toJson dimension).getObjVal? "type" with
    | .ok ty => ty == DataType.toJson .natural
    | _ => false)

  for draft in [dot, valid, invalid] do
    let encoded := JsonProtocol.valueToJson draft
    check "SumDraftRoundTrip" (match JsonProtocol.valueFromJson ExampleForms.Shapes.shape encoded with
      | .ok value => JsonProtocol.valueToJson value == encoded
      | _ => false)
  check "SumOnlyShowsActivePayload" ((fieldRefs ExampleForms.Shapes.form dot).isEmpty &&
    (fieldRefs ExampleForms.Shapes.form valid).map (·.indices) == [[2,0], [2,1]])
  check "SumPayloadLabels" ((fieldRefs ExampleForms.Shapes.form valid).map (·.labels) ==
    [["Shape", "rectangle", "Dimensions", "Width"], ["Shape", "rectangle", "Dimensions", "Height"]])
  for malformed in ["{}", "[0,[]]", "{\"tag\":3,\"value\":[]}",
      "{\"tag\":-1,\"value\":[]}", "{\"tag\":\"0\",\"value\":[]}",
      "{\"tag\":\"dot\",\"value\":false}", "{\"tag\":\"circle\",\"value\":false}",
      "{\"tag\":\"dot\",\"value\":{},\"extra\":true}"] do
    check "MalformedSumRejected" (match JsonProtocol.valueFromJson ExampleForms.Shapes.shape
        (← IO.ofExcept (Lean.Json.parse malformed)) with
      | .error _ => true
      | _ => false)

def main : IO Unit := do
  testDates
  testEditsAndVisibility
  testLabeledFields
  testPredicates
  testChoice
  testGroups
  testLists
  testSums
  let encoded := JsonProtocol.encode ExampleForms.Person.form ExampleForms.Person.initial
  let json ← IO.ofExcept (Lean.Json.parse encoded)
  let value ← IO.ofExcept (json.getObjVal? "value" >>= JsonProtocol.valueFromJson ExampleForms.Person.person)
  check "SpecificationValueRoundTrip" (JsonProtocol.valueToJson value == JsonProtocol.valueToJson ExampleForms.Person.initial)
  let fixture ← IO.FS.readFile "native/tui/tests/person.json"
  check "RustFixtureMatchesLeanSpecification" ((← IO.ofExcept (Lean.Json.parse fixture)).compress == encoded)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedNaturalRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (t := .natural) huge) == .ok huge)
  check "RejectsMalformedInterpreterResult"
    (match JsonProtocol.valueFromJson ExampleForms.Person.person (Lean.toJson "bad") with
      | .error _ => true
      | .ok _ => false)
