import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Person
import Forms.Runtime.Tui

open Forms Forms.Runtime

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def testEditsAndVisibility : IO Unit := do
  let initial := ExampleForms.Person.initial
  let form := ExampleForms.Person.form
  check "InitiallyVisibleFields" ((Form.fieldRefs form initial).length == 3)
  let visible := Path.set ExampleForms.Person.subscribed true initial
  check "SubscriptionShowsNestedAddress" ((Form.fieldRefs form visible).length == 5)
  let changed := Path.set ExampleForms.Person.number 42 visible
  check "NestedEditPreservesOtherFields" (JsonProtocol.valueToJson changed == Lean.Json.mkObj [("name", Lean.toJson "Ada"), ("subscribed", Lean.toJson true),
      ("address", Lean.Json.mkObj [("street", Lean.toJson "Lambda Lane"), ("number", Lean.toJson "42"), ("kind", Lean.toJson (0 : Nat))])])
  let hidden := Path.set ExampleForms.Person.subscribed false changed
  check "HidingPreservesNestedValue"
    ((Form.fieldRefs form hidden).length == 3 && Path.get ExampleForms.Person.number hidden == 42)
  check "ShowingRestoresEditedAddress"
    (JsonProtocol.valueToJson (Path.set ExampleForms.Person.subscribed true hidden) == JsonProtocol.valueToJson changed)

private def testLabeledFields : IO Unit := do
  let value := Path.set ExampleForms.Person.subscribed true ExampleForms.Person.initial
  let fields := Form.fieldRefs ExampleForms.Person.form value
  check "GeneratedLabelsFollowGroups"
    (List.map (fun field => Path.Labels.toList field.labels) fields ==
      [["Person", "Name"], ["Person", "Subscribed"],
       ["Person", "Address", "Street"],
       ["Person", "Address", "Number"],
       ["Person", "Address", "Kind"]])
  check "GeneratedPathsReadMatchingValues"
    (fields.map (fun field => JsonProtocol.valueToJson (Path.get field.path value)) == [Lean.toJson "Ada", Lean.toJson true, Lean.toJson "Lambda Lane", Lean.toJson "12", Lean.toJson (0 : Nat)])
  match fields[3]? with
  | none => throw (IO.userError "Missing generated number field")
  | some field =>
    match field with
    | ⟨.natural, path, _, _⟩ =>
      check "GeneratedPathEditsCorrectField" (JsonProtocol.valueToJson (Path.set path 42 value) ==
        JsonProtocol.valueToJson (Path.set ExampleForms.Person.number 42 value))
    | _ => throw (IO.userError "Expected a natural field")

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
        (JsonProtocol.valueToJson (type := .enum domain) value) == .ok value)
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
  check "DateComparison" (Expr.eval (root := .date) (.dateLe (.value early) (.project .self)) late)
  check "DateComparisonEqual" (Expr.eval (root := .date) (.dateLe (.value early) (.project .self)) early)
  check "DateComparisonReversed" (!Expr.eval (root := .date) (.dateLe (.value late) (.project .self)) early)

def main : IO Unit := do
  testDates
  testEditsAndVisibility
  testLabeledFields
  testPredicates
  testChoice
  testGroups
  let encoded := JsonProtocol.encode ExampleForms.Person.form ExampleForms.Person.initial
  let json ← IO.ofExcept (Lean.Json.parse encoded)
  let value ← IO.ofExcept (json.getObjVal? "value" >>= JsonProtocol.valueFromJson ExampleForms.Person.person)
  check "SpecificationValueRoundTrip" (JsonProtocol.valueToJson value == JsonProtocol.valueToJson ExampleForms.Person.initial)
  let fixture ← IO.FS.readFile "native/tui/tests/person.json"
  check "RustFixtureMatchesLeanSpecification" (fixture.trimAscii.toString == encoded)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedNaturalRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (type := .natural) huge) == .ok huge)
  check "RejectsMalformedInterpreterResult"
    (match JsonProtocol.valueFromJson ExampleForms.Person.person (Lean.toJson "bad") with
      | .error _ => true
      | .ok _ => false)
