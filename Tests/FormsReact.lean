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
  (key label : String)
  (input : Display.Editor)
  (messages : Option String := none)
  : Display.Control :=
  { key := ⟨key⟩, target := {}, label, disabled := false, location := [], input, messages }

def view : Display.View :=
  .stack (some "Person") [
    .control (control "name" "Name" (.text "Ada") (messages := some "Enter your name.")),
    .control (control "age" "Age" (.natural 36)),
    .hidden,
    .stack (some "") [.control (control "delivery" "Delivery" (.checkbox true))],
    .computed "Summary" "Ada, 36"]

def expected : FormsReact.Component :=
  .group {
    label := some "Person"
    children := [
      .textField {
        name := "name"
        label := "Name"
        value := "Ada"
        disabled := false
        error := some "Enter your name."
        onCommit := .apply "name" },
      .naturalField {
        name := "age"
        label := "Age"
        value := "36"
        disabled := false
        error := none
        onCommit := .apply "age" },
      .group {
        label := none
        children := [
          .checkbox {
            name := "delivery"
            label := "Delivery"
            checked := true
            disabled := false
            error := none
            onChange := .apply "delivery" }] },
      .output { label := "Summary", value := "Ada, 36" }] }

def run : IO Unit := do
  check "Lowering changed" (view.toReact false == some expected)
  check "Draft fields changed" (expected.draftFields == ["name", "age"])
  check "Hidden view must lower to nothing" (Display.View.hidden.toReact false == none)
  let pendingPage := view.toReactPage { Interaction.State.initial with submission := .pending } 3 "{}"
  check "Pending page must have no draft fields" pendingPage.draftFields.isEmpty
  let pending := match pendingPage with
    | .page page => page.busy && page.result.isNone && page.actions == 3 &&
        page.toolbar.all (fun
          | .button button => button.disabled
          | _ => false)
    | _ => false
  check "Pending page must be busy with disabled toolbar" pending
  let page := view.toReactPage { Interaction.State.initial with resultVisible := true } 0 "{}"
  let decoded : Except String FormsReact.Component := fromJson? (toJson page)
  check "Component JSON roundtrip changed" (decoded.toOption == some page)
  check "Props must encode directly under the constructor name"
    (((toJson expected).getObjVal? "group" >>= (·.getObjVal? "label")).toOption == some (toJson "Person"))
  let program := typescript% [FormsReact.Component]
  check "FormsReact types must generate one module" (program.modules.map (·.file) == ["FormsReact.ts"])
  IO.println "PASS FormsReact lowering and codecs"

end Tests.FormsReact
