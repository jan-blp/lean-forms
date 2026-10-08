import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Person
import Forms.Runtime.Tui

open Forms Forms.Runtime

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def testFields : IO Unit := do
  let fields := Form.fieldRefs ExampleForms.Person.form
  check "SingleField" (fields.length == 1)
  check "FieldLabel" (fields.map (fun field => Path.Labels.toList field.labels) == [["Name"]])
  check "RootPathReadsValue" (Path.get ExampleForms.Person.name ExampleForms.Person.initial == "Ada")
  check "RootPathReplacesValue" (Path.set ExampleForms.Person.name "Grace" ExampleForms.Person.initial == "Grace")

private def testPredicates : IO Unit := do
  let eligible : Expr .natural .boolean := .and (.value true) (.natLe (.value 10) (.project .self))
  check "EvaluatesTypedPredicate" (Expr.eval eligible 12)
  check "PredicateUsesEditedValue" (!(Expr.eval eligible 9))

def main : IO Unit := do
  testFields
  testPredicates
  let encoded := JsonProtocol.encode ExampleForms.Person.form ExampleForms.Person.initial
  let json ← IO.ofExcept (Lean.Json.parse encoded)
  let value ← IO.ofExcept (json.getObjVal? "value" >>= JsonProtocol.valueFromJson ExampleForms.Person.person)
  check "SpecificationValueRoundTrip" (value == ExampleForms.Person.initial)
  let fixture ← IO.FS.readFile "native/tui/tests/person.json"
  check "RustFixtureMatchesLeanSpecification" (fixture.trimAscii.toString == encoded)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedNaturalRoundTrip"
    (JsonProtocol.valueFromJson .natural (JsonProtocol.valueToJson (type := .natural) huge) == .ok huge)
  check "RejectsMalformedInterpreterResult"
    (match JsonProtocol.valueFromJson ExampleForms.Person.person (Lean.toJson (42 : Nat)) with
      | .error _ => true
      | .ok _ => false)
