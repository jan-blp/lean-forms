import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Person
import Forms.Technology.Input
import Forms.Technology.Terminal
import Forms.Technology.Tui

open Forms Forms.Technology

private def check (name : String) (passed : Bool) : IO Unit := do
  if passed then IO.println ("PASS " ++ name)
  else throw (IO.userError ("FAIL " ++ name))

private def testEditsAndVisibility : IO Unit := do
  let initial := ExampleForms.Person.initial
  let form := ExampleForms.Person.form
  check "InitiallyShowsNameAndSubscription" (List.length (Form.fieldRefs form initial) == 2)
  let subscription : FieldRef ExampleForms.Person.schema :=
    { type := .boolean
      path := ExampleForms.Person.subscribed
      labels := ("Person", "Newsletter", "Subscribed")
      control := .checkbox }
  match edit subscription "true" initial with
  | .error error => throw (IO.userError (InputError.message error))
  | .ok visible =>
    check "SubscriptionShowsNestedAddress" (List.length (Form.fieldRefs form visible) == 4)
    let houseNumber : FieldRef ExampleForms.Person.schema :=
      { type := .natural
        path := ExampleForms.Person.number
        labels := ("Person", "Newsletter", "Address", "Number")
        control := .natural }
    match edit houseNumber "42" visible with
    | .error error => throw (IO.userError (InputError.message error))
    | .ok changed =>
      check "NestedEditPreservesOtherFields"
        (changed == ("Ada", (true, ("Lambda Lane", 42))))
      match edit subscription "false" changed with
      | .error error => throw (IO.userError (InputError.message error))
      | .ok hidden =>
        check "HidingPreservesNestedValue"
          (List.length (Form.fieldRefs form hidden) == 2 && Path.get ExampleForms.Person.number hidden == 42)
        match edit subscription "true" hidden with
        | .error error => throw (IO.userError (InputError.message error))
        | .ok shown => check "ShowingRestoresEditedAddress" (shown == changed)

private def testLabeledFields : IO Unit := do
  let value := Path.set ExampleForms.Person.subscribed true ExampleForms.Person.initial
  let fields := Form.fieldRefs ExampleForms.Person.form value
  check "GeneratedLabelsFollowGroups"
    (List.map (fun field => Path.Labels.toList field.labels) fields ==
      [["Person", "Name"], ["Person", "Newsletter", "Subscribed"],
       ["Person", "Newsletter", "Address", "Street"],
       ["Person", "Newsletter", "Address", "Number"]])
  check "GeneratedPathsReadMatchingValues"
    (List.map (fun field => display field.control (Path.get field.path value)) fields ==
      ["Ada", "true", "Lambda Lane", "12"])
  match fields[3]? with
  | none => throw (IO.userError "Missing generated number field")
  | some field =>
    match edit field "42" value with
    | .error error => throw (IO.userError (InputError.message error))
    | .ok changed =>
      check "GeneratedPathEditsCorrectField"
        (changed == ("Ada", (true, ("Lambda Lane", 42))))

private def testInput : IO Unit := do
  check "RejectsInvalidBooleans" (match parse .checkbox "yes" with
    | .error .expectedBoolean => true
    | _ => false)
  for input in ["-1", "1.5", "", "abc"] do
    check ("RejectsInvalidNatural " ++ reprStr input) (match parse .natural input with
      | .error .expectedNatural => true
      | _ => false)
  check "PreservesTextWhitespace" (match parse .text " Ada " with
    | .ok value => value == " Ada "
    | .error _ => false)
  check "AcceptsZero" (match parse .natural "0" with
    | .ok value => value == 0
    | .error _ => false)

private def testPredicates : IO Unit := do
  let eligible : Expr ExampleForms.Person.schema .boolean :=
    .and (.textEquals (.project ExampleForms.Person.name) (.value "Ada"))
      (.natLe (.value 10) (.project ExampleForms.Person.number))
  check "EvaluatesTypedPredicate" (Expr.eval eligible ExampleForms.Person.initial)
  check "PredicateUsesEditedValue"
    (!(Expr.eval eligible (Path.set ExampleForms.Person.number 9 ExampleForms.Person.initial)))

private structure Script where
  input : List String
  output : List String := []

private instance : MonadTerminal (StateM Script) where
  putStr text := modify fun script =>
    { script with
      output := script.output ++ [text] }
  readLine := do
    let script ← get
    match script.input with
    | [] => return none
    | line :: rest =>
      set { script with
        input := rest }
      return some line

private def testTerminal : IO Unit := do
  let initial := ExampleForms.Person.initial
  let form := ExampleForms.Person.form
  let (edited, script) := StateT.run (Terminal.run (m := StateM Script) form initial)
    { input := ["0", "2", "yes", "2", "true", "4", "42", "q"] }
  check "TerminalEditsThroughCapabilities"
    (edited == ("Ada", (true, ("Lambda Lane", 42))) && script.input == [])
  check "TerminalReportsInvalidSelection"
    (List.contains script.output "Choose one of the displayed field numbers.\n")
  check "TerminalReportsInvalidInput"
    (List.contains script.output "Enter true or false.\n")
  let (unchanged, _) := StateT.run (Terminal.run (m := StateM Script) form initial)
    { input := ["1"] }
  check "TerminalPreservesValueAtEndOfInput" (unchanged == initial)
  let (blankName, _) := StateT.run (Terminal.run (m := StateM Script) form initial)
    { input := ["1", ""] }
  check "TerminalDistinguishesBlankLineFromEndOfInput"
    (blankName == ("", (false, ("Lambda Lane", 12))))

def main : IO Unit := do
  testEditsAndVisibility
  testLabeledFields
  testInput
  testPredicates
  testTerminal
  let encoded := Specification.encode ExampleForms.Person.form ExampleForms.Person.initial
  let json ← IO.ofExcept (Lean.Json.parse encoded)
  let value ← IO.ofExcept (json.getObjVal? "value" >>= Specification.valueFromJson ExampleForms.Person.schema)
  check "SpecificationValueRoundTrip" (value == ExampleForms.Person.initial)
  let fixture ← IO.FS.readFile "native/ratatui/tests/person.json"
  check "RustFixtureMatchesLeanSpecification" (fixture.trimAscii.toString == encoded)
  let huge := 12345678901234567890123456789012345678901234567890
  check "UnboundedNaturalRoundTrip"
    (Specification.valueFromJson .natural (Specification.valueToJson (type := .natural) huge) == .ok huge)
  check "RejectsMalformedInterpreterResult"
    (match Specification.valueFromJson ExampleForms.Person.schema (Lean.toJson "bad") with
      | .error _ => true
      | .ok _ => false)
