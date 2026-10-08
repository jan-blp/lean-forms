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

private structure TuiScript where
  keys : List Key
  frames : List Screen := []
  events : List String := []

private instance : MonadTui (StateM TuiScript) where
  withSession action := do
    modify fun script => { script with
      events := script.events ++ ["open"] }
    let result ← action
    modify fun script => { script with
      events := script.events ++ ["close"] }
    return result
  readKey := do
    let script ← get
    match script.keys with
    | [] => return .quit
    | key :: rest =>
      set { script with
        keys := rest }
      return key
  screenSize := pure {
    columns := 80
    rows := 24
  }
  draw lines := modify fun script =>
    { script with
      frames := script.frames ++ [lines] }

private def testTui : IO Unit := do
  let form := ExampleForms.Person.form
  let initial := ExampleForms.Person.initial
  let (value, script) := StateT.run (Tui.run (m := StateM TuiScript) form initial) {
    keys := [.up, .down, .character ' ', .down, .down, .down,
      .enter, .clear, .character '-', .enter,
      .clear, .character '4', .character '2', .enter,
      .up, .up, .character ' ', .character ' ', .quit]
  }
  check "TuiClosesSession" (script.events == ["open", "close"])
  check "TuiEditsAndPreservesHiddenValues"
    (value == ("Ada", (true, ("Lambda Lane", 42))) && List.isEmpty script.keys)
  check "TuiShowsValidationErrors"
    (List.any script.frames (fun screen =>
      match screen.editor with
      | some editor => editor.error == some (InputError.message .expectedNatural)
      | none => false))
  let (cancelled, _) := StateT.run (Tui.run (m := StateM TuiScript) form initial) {
    keys := [.enter, .clear, .character 'x', .escape, .quit]
  }
  check "TuiCancelDiscardsDraft" (cancelled == initial)
  let (blank, _) := StateT.run (Tui.run (m := StateM TuiScript) form initial) {
    keys := [.enter, .clear, .enter, .quit]
  }
  check "TuiSavesEmptyText" (Path.get ExampleForms.Person.name blank == "")
  let (unicode, _) := StateT.run (Tui.run (m := StateM TuiScript) form initial) {
    keys := [.enter, .clear, .character 'é', .backspace, .character 'q', .enter, .quit]
  }
  check "TuiBackspaceAndLiteralQuitCharacter" (Path.get ExampleForms.Person.name unicode == "q")
  let (vim, _) := StateT.run (Tui.run (m := StateM TuiScript) form initial) {
    keys := [.character 'j', .character ' ', .character 'k', .character 'i',
      .clear, .character 'j', .character 'k', .character 'i', .enter, .character 'q']
  }
  check "TuiVimKeysNavigateAndRemainLiteralWhileEditing"
    (vim == ("jki", (true, ("Lambda Lane", 12))))
  let (unfinished, _) := StateT.run (Tui.run (m := StateM TuiScript) form initial) {
    keys := [.enter, .clear, .character 'x', .quit]
  }
  check "TuiQuitDiscardsDraft" (unfinished == initial)
  let visible := Path.set ExampleForms.Person.subscribed true initial
  let screen := Tui.screen form {
    value := visible
    selected := 3
  }
  check "TuiProvidesStructuredFieldsToRenderer"
    (screen.selected == 3 && List.length screen.fields == 4 &&
      List.map (fun field => field.value) screen.fields == ["Ada", "[x]", "Lambda Lane", "12"])

def main : IO Unit := do
  testEditsAndVisibility
  testLabeledFields
  testInput
  testPredicates
  testTerminal
  testTui
