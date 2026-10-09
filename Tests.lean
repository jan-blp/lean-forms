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
  check "NestedEditPreservesOtherFields" (JsonProtocol.valueToJson changed == Lean.Json.arr #[Lean.toJson "Ada", Lean.toJson true,
      Lean.Json.arr #[Lean.toJson "Lambda Lane", Lean.toJson "42", Lean.toJson (0 : Nat)]])
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
  let eligible : Expr ExampleForms.Person.schema .boolean :=
    .and (.value true)
      (.natLe (.value 10) (.project ExampleForms.Person.number))
  check "EvaluatesTypedPredicate" (Expr.eval eligible ExampleForms.Person.initial)
  check "PredicateUsesEditedValue"
    (!(Expr.eval eligible (Path.set ExampleForms.Person.number 9 ExampleForms.Person.initial)))

private def testChoice : IO Unit := do
  let domain := ExampleForms.Person.addressChoices
  for value in FinEnum.toList domain.type do
    check "ChoiceRoundTripPreservesEnumValue"
      (JsonProtocol.valueFromJson (.choice domain)
        (JsonProtocol.valueToJson (type := .choice domain) value) == .ok value)
  check "ChoiceDisplaysEnumLabel" (domain.label .work == "Work")
  for json in [Lean.toJson (3 : Nat), Lean.toJson (-1 : Int), Lean.toJson "1", Lean.Json.null] do
    check "RejectsInvalidChoiceResult"
      (match JsonProtocol.valueFromJson (.choice domain) json with
        | .error _ => true
        | .ok _ => false)

private def testGroups : IO Unit := do
  let empty : DataType := .group (n := 0) Fin.elim0
  let emptyValue ← IO.ofExcept (JsonProtocol.valueFromJson empty (.arr #[]))
  check "EmptyGroupRoundTrip" (JsonProtocol.valueToJson emptyValue == .arr #[])
  let singleton : DataType := .group ![.text]
  let singleValue ← IO.ofExcept (JsonProtocol.valueFromJson singleton (.arr #[Lean.toJson "only"]))
  check "SingleChildGroupRoundTrip" (JsonProtocol.valueToJson singleValue == .arr #[Lean.toJson "only"])
  for json in [Lean.Json.arr #[], .arr #[Lean.toJson "one", Lean.toJson "two"],
      .arr #[Lean.toJson true]] do
    check "RejectsWrongGroupLengthOrChildType"
      (match JsonProtocol.valueFromJson singleton json with
      | .error _ => true
      | .ok _ => false)
  let addressPath : Path ExampleForms.Person.schema ExampleForms.Person.address := .child 2 .here
  let numberPath : Path ExampleForms.Person.address .natural := .child 1 .here
  check "ComposedGroupPath"
    ((addressPath.trans numberPath).toList == [2, 1] &&
      (addressPath.trans numberPath).get ExampleForms.Person.initial == 12)

def main : IO Unit := do
  testEditsAndVisibility
  testLabeledFields
  testPredicates
  testChoice
  testGroups
  let encoded := JsonProtocol.encode ExampleForms.Person.form ExampleForms.Person.initial
  let json ← IO.ofExcept (Lean.Json.parse encoded)
  let value ← IO.ofExcept (json.getObjVal? "value" >>= JsonProtocol.valueFromJson ExampleForms.Person.schema)
  check "SpecificationValueRoundTrip" (JsonProtocol.valueToJson value == JsonProtocol.valueToJson ExampleForms.Person.initial)
  let fixture ← IO.FS.readFile "native/tui/tests/person.json"
  check "RustFixtureMatchesLeanSpecification" (fixture.trimAscii.toString == encoded)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedNaturalRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (type := .natural) huge) == .ok huge)
  check "RejectsMalformedInterpreterResult"
    (match JsonProtocol.valueFromJson ExampleForms.Person.schema (Lean.toJson "bad") with
      | .error _ => true
      | .ok _ => false)
