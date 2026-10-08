import Forms.Runtime.FormSnapshot
import Mathlib.Data.Nat.Basic
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
  check "GeneratedPathsSelectMatchingFields"
    (fields.map (·.indices) == [[0], [1], [2,0], [2,1], [2,2]])

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
  check "DateComparison" (Expr.eval (input := .date) (.dateLe (.value early) (.project .self)) late)
  check "DateComparisonEqual" (Expr.eval (input := .date) (.dateLe (.value early) (.project .self)) early)
  check "DateComparisonReversed" (!Expr.eval (input := .date) (.dateLe (.value late) (.project .self)) early)

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
  check "RustFixtureMatchesLeanSpecification" ((Lean.Json.parse fixture).toOption == (Lean.Json.parse encoded).toOption)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedNaturalRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (type := .natural) huge) == .ok huge)
  check "RejectsMalformedInterpreterResult"
    (match JsonProtocol.valueFromJson ExampleForms.Person.person (Lean.toJson "bad") with
      | .error _ => true
      | .ok _ => false)
