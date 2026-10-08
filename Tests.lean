import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Person
import Forms.Runtime.Tui

open Forms Forms.Runtime

private def personTuple (value : DataType.denote ExampleForms.Person.schema) : String × Bool × String × Nat :=
  (ExampleForms.Person.name.get value, ExampleForms.Person.subscribed.get value,
    ExampleForms.Person.street.get value, ExampleForms.Person.number.get value)

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def testEditsAndVisibility : IO Unit := do
  let initial := ExampleForms.Person.initial
  let form := ExampleForms.Person.form
  check "InitiallyVisibleFields" ((Form.fieldRefs form initial).length == 2)
  let visible := Path.set ExampleForms.Person.subscribed true initial
  check "SubscriptionShowsNestedAddress" ((Form.fieldRefs form visible).length == 4)
  let changed := Path.set ExampleForms.Person.number 42 visible
  check "NestedEditPreservesOtherFields" (personTuple changed == ("Ada", (true, ("Lambda Lane", 42))))
  let hidden := Path.set ExampleForms.Person.subscribed false changed
  check "HidingPreservesNestedValue"
    ((Form.fieldRefs form hidden).length == 2 && Path.get ExampleForms.Person.number hidden == 42)
  check "ShowingRestoresEditedAddress"
    (personTuple (Path.set ExampleForms.Person.subscribed true hidden) == personTuple changed)

private def testLabeledFields : IO Unit := do
  let value := Path.set ExampleForms.Person.subscribed true ExampleForms.Person.initial
  let fields := Form.fieldRefs ExampleForms.Person.form value
  check "GeneratedLabelsFollowGroups"
    (List.map (fun field => Path.Labels.toList field.labels) fields ==
      [["Person", "Name"], ["Person", "Subscribed"],
       ["Person", "Address", "Street"],
       ["Person", "Address", "Number"]])
  check "GeneratedPathsReadMatchingValues"
    (fields.map (fun field => JsonProtocol.valueToJson (Path.get field.path value)) == [Lean.toJson "Ada", Lean.toJson true, Lean.toJson "Lambda Lane", Lean.toJson "12"])
  match fields[3]? with
  | none => throw (IO.userError "Missing generated number field")
  | some field =>
    match field with
    | ⟨.natural, path, _, _⟩ =>
      check "GeneratedPathEditsCorrectField" (personTuple (Path.set path 42 value) == ("Ada", (true, ("Lambda Lane", 42))))
    | _ => throw (IO.userError "Expected a natural field")

private def testPredicates : IO Unit := do
  let eligible : Expr ExampleForms.Person.schema .boolean :=
    .and (.value true)
      (.natLe (.value 10) (.project ExampleForms.Person.number))
  check "EvaluatesTypedPredicate" (Expr.eval eligible ExampleForms.Person.initial)
  check "PredicateUsesEditedValue"
    (!(Expr.eval eligible (Path.set ExampleForms.Person.number 9 ExampleForms.Person.initial)))

def main : IO Unit := do
  testEditsAndVisibility
  testLabeledFields
  testPredicates
  let encoded := JsonProtocol.encode ExampleForms.Person.form ExampleForms.Person.initial
  let json ← IO.ofExcept (Lean.Json.parse encoded)
  let value ← IO.ofExcept (json.getObjVal? "value" >>= JsonProtocol.valueFromJson ExampleForms.Person.schema)
  check "SpecificationValueRoundTrip" (personTuple value == personTuple ExampleForms.Person.initial)
  let fixture ← IO.FS.readFile "native/tui/tests/person.json"
  check "RustFixtureMatchesLeanSpecification" (fixture.trimAscii.toString == encoded)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedNaturalRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (type := .natural) huge) == .ok huge)
  check "RejectsMalformedInterpreterResult"
    (match JsonProtocol.valueFromJson ExampleForms.Person.schema (Lean.toJson "bad") with
      | .error _ => true
      | .ok _ => false)
