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
    .control (control (.edit [.field "name"]) "Name" (.text .plain "Ada")
      (messages := [{ kind := .error, text := "Enter your name." }])),
    .control (control (.edit [.field "age"]) "Age" (.text .natural "36")),
    .hidden,
    .stack (some "") [.control (control (.edit [.field "delivery"]) "Delivery" (.checkbox true))],
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
        disabled := false
        errors := ["Enter your name."]
        checks := none
        onCommit := .apply "[\"edit\",\"name\"]" },
      .textField {
        name := "[\"edit\",\"age\"]"
        label := "Age"
        kind := .natural
        value := "36"
        disabled := false
        errors := []
        checks := none
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
            checks := none
            onChange := .apply "[\"edit\",\"delivery\"]" }]
        errors := []
        checks := none
        key := none },
      .output { label := "Summary", value := "Ada, 36" }]
    errors := []
    checks := none
    key := none }

def run : IO Unit := do
  check "Lowering changed" (view.toReact false == some expected)
  check "Draft fields changed" (expected.draftFields == ["[\"edit\",\"name\"]", "[\"edit\",\"age\"]"])
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
