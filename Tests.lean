import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Person
import Forms.Runtime.Tui

open Forms Forms.Runtime

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def testFields : IO Unit := do
  let fields := Form.fieldRefs ExampleForms.Person.form ExampleForms.Person.initial
  check "SingleField" (fields.length == 1)
  check "FieldLabel" (fields.map (fun field => Path.Labels.toList field.labels) == [["Kind"]])
  check "RootPathReadsValue" (Path.get ExampleForms.Person.kind ExampleForms.Person.initial == .home)
  check "RootPathReplacesValue" (Path.set ExampleForms.Person.kind .work ExampleForms.Person.initial == .work)

private def testPredicates : IO Unit := do
  let eligible : Expr .natural .boolean := .and (.value true) (.natLe (.value 10) (.project .self))
  check "EvaluatesTypedPredicate" (Expr.eval eligible 12)
  check "PredicateUsesEditedValue" (!(Expr.eval eligible 9))

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
  testFields
  testPredicates
  testChoice
  let encoded := JsonProtocol.encode ExampleForms.Person.form ExampleForms.Person.initial
  let json ← IO.ofExcept (Lean.Json.parse encoded)
  let value ← IO.ofExcept (json.getObjVal? "value" >>= JsonProtocol.valueFromJson ExampleForms.Person.schema)
  check "SpecificationValueRoundTrip" (value == ExampleForms.Person.initial)
  let fixture ← IO.FS.readFile "native/tui/tests/person.json"
  check "RustFixtureMatchesLeanSpecification" (fixture.trimAscii.toString == encoded)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedNaturalRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (type := .natural) huge) == .ok huge)
  check "RejectsMalformedInterpreterResult"
    (match JsonProtocol.valueFromJson ExampleForms.Person.schema (Lean.toJson (42 : Nat)) with
      | .error _ => true
      | .ok _ => false)
