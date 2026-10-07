import Mathlib.Data.Nat.Basic
import Forms.ExampleForms.Person
import Forms.Runtime.Input
import Forms.Runtime.Terminal

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

private def testInput : IO Unit := do
  check "RejectsInvalidBooleans" (match parse .checkbox "yes" with
    | .error .expectedBoolean => true
    | _ => false)
  for input in ["-1", "1.5", "", "abc"] do
    check ("RejectsInvalidNatural " ++ reprStr input) (match parse .naturalInput input with
      | .error .expectedNatural => true
      | _ => false)
  check "PreservesTextWhitespace" (match parse .textInput " Ada " with
    | .ok value => value == " Ada "
    | .error _ => false)
  check "AcceptsZero" (match parse .naturalInput "0" with
    | .ok value => value == 0
    | .error _ => false)

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
    { input := ["0", "1", "Grace", "q"] }
  check "TerminalEditsThroughCapabilities" (edited == "Grace" && script.input == [])
  check "TerminalReportsInvalidSelection"
    (List.contains script.output "Choose one of the displayed field numbers.\n")
  let (unchanged, _) := StateT.run (Terminal.run (m := StateM Script) form initial)
    { input := ["1"] }
  check "TerminalPreservesValueAtEndOfInput" (unchanged == initial)
  let (blankName, _) := StateT.run (Terminal.run (m := StateM Script) form initial)
    { input := ["1", ""] }
  check "TerminalDistinguishesBlankLineFromEndOfInput" (blankName == "")
  let (number, errors) := StateT.run
    (Terminal.run (m := StateM Script) (Form.field "Number" Widget.naturalInput) 12)
    { input := ["1", "-1", "1", "42", "q"] }
  check "TerminalValidatesNaturalInput" (number == 42)
  check "TerminalReportsInvalidInput"
    (List.contains errors.output "Enter a non-negative whole number.\n")

def main : IO Unit := do
  testFields
  testInput
  testPredicates
  testTerminal
