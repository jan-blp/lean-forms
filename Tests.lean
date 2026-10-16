import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Person
import Forms.Runtime.Tui

open Forms Forms.Runtime

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def testEditsAndVisibility : IO Unit := do
  let initial := ExampleForms.Person.initial
  let form := ExampleForms.Person.form
  check "InitiallyVisibleFields" ((Form.fieldRefs form initial initial).length == 3)
  let visible := Path.set ExampleForms.Person.subscribed true initial
  check "SubscriptionShowsNestedAddress" ((Form.fieldRefs form visible visible).length == 5)
  let changed := Path.set ExampleForms.Person.number 42 visible
  check "NestedEditPreservesOtherFields" (JsonProtocol.valueToJson changed == Lean.Json.mkObj [("name", Lean.toJson "Ada"), ("subscribed", Lean.toJson true),
      ("address", Lean.Json.mkObj [("street", Lean.toJson "Lambda Lane"), ("number", Lean.toJson "42"), ("kind", Lean.toJson (0 : Nat))])])
  let hidden := Path.set ExampleForms.Person.subscribed false changed
  check "HidingPreservesNestedValue"
    ((Form.fieldRefs form hidden hidden).length == 3 && Path.get ExampleForms.Person.number hidden == 42)
  check "ShowingRestoresEditedAddress"
    (JsonProtocol.valueToJson (Path.set ExampleForms.Person.subscribed true hidden) == JsonProtocol.valueToJson changed)

private def testLabeledFields : IO Unit := do
  let value := Path.set ExampleForms.Person.subscribed true ExampleForms.Person.initial
  let fields := Form.fieldRefs ExampleForms.Person.form value value
  check "GeneratedLabelsFollowGroups"
    (List.map (fun field => field.labels) fields ==
      [["Person", "Name"], ["Person", "Subscribed"],
       ["Person", "Address", "Street"],
       ["Person", "Address", "Number"],
       ["Person", "Address", "Kind"]])
  check "GeneratedFieldIndices"
    (fields.map (·.indices) == [[0], [1], [2, 0], [2, 1], [2, 2]])

private def testPredicates : IO Unit := do
  let eligible : Expr ExampleForms.Person.schema .boolean :=
    .and (.value true)
      (.natLe (.value 10) (.project ExampleForms.Person.number))
  check "EvaluatesTypedPredicate" (Expr.eval eligible ExampleForms.Person.initial)
  check "PredicateUsesEditedValue"
    (!(Expr.eval eligible (Path.set ExampleForms.Person.number 9 ExampleForms.Person.initial)))

private def testChoice : IO Unit := do
  let domain := ExampleForms.Person.addressEnum
  for value in FinEnum.toList domain.type do
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
  let addressPath : Path ExampleForms.Person.schema ExampleForms.Person.address := .child .address .self
  let numberPath : Path ExampleForms.Person.address .natural := .child .number .self
  check "ComposedGroupPath"
    ((addressPath.trans numberPath).toList == ["address", "number"] &&
      (addressPath.trans numberPath).get ExampleForms.Person.initial == 12)

private def testLists : IO Unit := do
  let initial := ExampleForms.Invoice.initial
  check "ListRoundTrip"
    (match JsonProtocol.valueFromJson ExampleForms.Invoice.shape (JsonProtocol.valueToJson initial) with
    | .ok value => JsonProtocol.valueToJson value == JsonProtocol.valueToJson initial
    | .error _ => false)
  check "ListFieldIndices"
    ((ExampleForms.Invoice.form.fieldRefs initial initial).map (·.indices) == [[0, 0], [0, 1], [0, 2]])
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
    (fixture.trimAscii.toString == JsonProtocol.encode ExampleForms.Invoice.form initial)

def main : IO Unit := do
  testEditsAndVisibility
  testLabeledFields
  testPredicates
  testChoice
  testGroups
  testLists
  let encoded := JsonProtocol.encode ExampleForms.Person.form ExampleForms.Person.initial
  let json ← IO.ofExcept (Lean.Json.parse encoded)
  let value ← IO.ofExcept (json.getObjVal? "value" >>= JsonProtocol.valueFromJson ExampleForms.Person.schema)
  check "SpecificationValueRoundTrip" (JsonProtocol.valueToJson value == JsonProtocol.valueToJson ExampleForms.Person.initial)
  let fixture ← IO.FS.readFile "native/tui/tests/person.json"
  check "RustFixtureMatchesLeanSpecification" (fixture.trimAscii.toString == encoded)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedNaturalRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (t := .natural) huge) == .ok huge)
  check "RejectsMalformedInterpreterResult"
    (match JsonProtocol.valueFromJson ExampleForms.Person.schema (Lean.toJson "bad") with
      | .error _ => true
      | .ok _ => false)
