module

public import Forms.Runtime.ReactView
import Forms.Protocol.TypeScriptAst
meta import Forms.Protocol.TypeScript

public section
namespace Tests.FormsReact
open Lean Forms.Runtime Forms.Protocol

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError message)

private def control
  (key : ControlKey)
  (label : String)
  (input : Display.Editor)
  (messages : List Forms.Model.Message := [])
  : Display.Control :=
  { key, target := {}, label, disabled := false, location := [], input, messages }

def view : Display.View :=
  .stack (some "Person") [
    .control (control (.edit [.field "name"]) "Name"
      (.field (.text .plain "Ada" .onLeave) (.linked { page := 1, cellIds := [3, 4], text := "Ada" } false))
      (messages := [{ kind := .error, text := "Enter your name." }])),
    .control (control (.edit [.field "age"]) "Age" (.field (.text .natural "36" .onLeave) .unsupported)),
    .hidden,
    .stack (some "") [.control (control (.edit [.field "delivery"]) "Delivery"
      (.field (.checkbox true) .missing))],
    .computed "Summary" "Ada, 36"]

def expected : FormsReact.Component :=
  .group {
    label := some "Person"
    children := [
      .textField {
        name := "[\"edit\",\"name\"]"
        label := "Name"
        kind := .plain
        value := "Ada"
        commit := .onLeave
        disabled := false
        errors := ["Enter your name."]
        evidence := .linked 1 [3, 4] false
        onCommit := .apply "[\"edit\",\"name\"]" },
      .textField {
        name := "[\"edit\",\"age\"]"
        label := "Age"
        kind := .natural
        value := "36"
        commit := .onLeave
        disabled := false
        errors := []
        evidence := .unsupported
        onCommit := .apply "[\"edit\",\"age\"]" },
      .group {
        label := none
        children := [
          .checkbox {
            name := "[\"edit\",\"delivery\"]"
            label := "Delivery"
            checked := true
            disabled := false
            errors := []
            evidence := .missing
            onChange := .apply "[\"edit\",\"delivery\"]" }]
        errors := []
        key := none },
      .output { label := "Summary", value := "Ada, 36" }]
    errors := []
    key := none }

def run : IO Unit := do
  check "Lowering changed" (view.toReact false == some expected)
  check "Draft fields changed" (expected.draftFields == ["[\"edit\",\"name\"]", "[\"edit\",\"age\"]"])
  check "Pick fields changed"
    (expected.pickFields == ["[\"edit\",\"name\"]", "[\"edit\",\"delivery\"]"])
  check "Hidden view must lower to nothing" (Display.View.hidden.toReact false == none)
  check "Buttons must lower to press"
    ((control (.press [0] []) "Add" .action).toReact false ==
      .button { label := "Add", variant := .secondary, disabled := false, onClick := .press "[\"press\",[0],[]]" })
  let pendingPage := view.toReactPage { Interaction.State.initial with pending := true } "{}"
  check "Pending page must have no draft fields" pendingPage.draftFields.isEmpty
  let pending := match pendingPage with
    | .page page => page.busy && page.result.isNone &&
        page.toolbar.all (fun
          | .button button => button.disabled
          | _ => false)
    | _ => false
  check "Pending page must be busy with disabled toolbar" pending
  let page := view.toReactPage { Interaction.State.initial with resultVisible := true } "{}"
  let decoded : Except String FormsReact.Component := fromJson? (toJson page)
  check "Component JSON roundtrip changed" (decoded.toOption == some page)
  check "Props must encode directly under the constructor name"
    (((toJson expected).getObjVal? "group" >>= (·.getObjVal? "label")).toOption == some (toJson "Person"))
  let program := typescript% [FormsReact.Component]
  check "FormsReact types must generate one module" (program.modules.map (·.file) == ["FormsReact.ts"])
  IO.println "PASS FormsReact lowering and codecs"

end Tests.FormsReact
