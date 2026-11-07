module

public import Forms.Runtime.CompiledRevision
public import Tests.ServerRefinements

@[expose] public section

namespace Tests.CompiledForms
open Lean Forms Forms.Runtime Forms.ExampleForms Forms.Composition

def check (message : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError message)

def request (operation handle : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj ([("operation", toJson operation), ("handle", toJson handle)] ++ fields)

def execute (store : CompiledForms.Store) (request : Json) : Except String (CompiledForms.Store × Json) := do
  let (store, response) ← CompiledFormsProtocol.execute compiledRevision store request
  pure (store, CompiledFormsProtocol.responseToJson response)

def openRequest (selected : Example) (revision := compiledRevision) : Json :=
  Json.mkObj [("operation", toJson "open"), ("form", toJson selected.name),
    ("revision", toJson revision), ("value", JsonProtocol.valueToJson selected.definition.initial)]

def editorNode (control : Display.Control) : IO DisplayLayout.Node :=
  match DisplayLayout.control {} control with
  | .element .form _ _ (.element .label _ _ [input] _ :: _) _ => pure input
  | _ => throw (IO.userError "Missing editor input")

def testFormatting : IO Unit := do
  check "FormatTextIsLiteral" (CompiledView.formatValue (ty := .text) "<img src=x> 🌍\x00" == "<img src=x> 🌍\x00")
  check "FormatNaturalPrecision" (CompiledView.formatValue (ty := .natural) 123456789012345678901234567890 == "123456789012345678901234567890")
  check "FormatBooleanList" (CompiledView.formatValue (ty := .list .boolean) [true, false] == "[true, false]")
  check "FormatEmptyList" (CompiledView.formatValue (ty := .list .text) [] == "[]")
  check "FormatNestedList" (CompiledView.formatValue (ty := .list (.list .natural)) [[], [1, 2]] == "[[], [1, 2]]")
  check "FormatEnumLabel" (CompiledView.formatValue (ty := Person.addressKind) .work == "Work")
  check "FormatNestedRecord" (CompiledView.formatValue Person.draft ==
    "{name: Ada, age: 28, subscribed: false, address: {street: Lambda Lane, kind: Home}}")
  check "FormatSumPayload" (CompiledView.formatValue (ty := Shapes.shape) ⟨.circle, 3⟩ == "circle: 3")
  let date ← IO.ofExcept (JsonProtocol.valueFromJson .date (.str "2028-02-29"))
  check "FormatDate" (CompiledView.formatValue date == "2028-02-29")
  let computed := CompiledView.render (.computed (state := .natural) "Person" (.value Person.draft)) 0
  check "ComputedDisplayText" (match computed.view with
    | .computed _ text => text == CompiledView.formatValue Person.draft
    | _ => false)
  check "ComputedHasNoSchema" (((DisplayProtocol.viewToJson computed.view).getObjVal? "schema").toOption.isNone)
  let editor := CompiledView.editor Widget.select (ty := Person.addressKind) .work [] [] "replace" "Kind" false
  let input := DisplayProtocol.layoutToJson (← editorNode editor.view)
  let options ← IO.ofExcept (input.getObjValAs? (Array Json) "children")
  check "SelectOptionsHaveLabels" (options.toList.map (fun option => (option.getObjValAs? String "text").toOption) ==
    [some "Home", some "Work", some "Other"])
  check "SelectValueIsDOMIndex" ((input.getObjValAs? String "value").toOption == some "1")
  let bindings ← IO.ofExcept (input.getObjValAs? (Array Json) "bindings")
  check "SelectArgumentIsNumeric" ((bindings[0]!.getObjValAs? String "argument").toOption == some "index")
  check "EditorHasNoSchema" (((DisplayProtocol.controlToJson editor.view).getObjVal? "schema").toOption.isNone)

def testDisplay : IO Unit := do
  let natural := CompiledView.editor Widget.naturalInput 123456789012345678901234567890
    [.name "items", .index 2] [.field "items", .item 2] "replace" "Count" false
  check "Natural display retains a typed value" (match natural.view.body with
    | .editor _ (.natural value) => value == 123456789012345678901234567890
    | _ => false)
  let encoded := DisplayProtocol.controlToJson natural.view
  check "Natural serializes without precision loss"
    (((DisplayProtocol.layoutToJson (← editorNode natural.view)).getObjValAs? String "value").toOption == some "123456789012345678901234567890")
  check "Control target distinguishes names and numeric indices"
    ((encoded.getObjVal? "target").toOption == some (toJson [toJson "items", toJson (2 : Nat)]))
  check "Absent messages remain absent" ((encoded.getObjVal? "messages").toOption.isNone)
  let withMessage := DisplayProtocol.controlToJson { natural.view with messages := some "" }
  check "Empty messages remain present" ((withMessage.getObjValAs? String "messages").toOption == some "")
  for view in [Display.View.hidden, .stack none [], .stack (some "") [], .text "Text", .table [] []] do
    check "Unlabelled view uses fallback title" (view.title == "Form")
  for view in [Display.View.control natural.view, .stack (some "Count") [], .computed "Count" "0"] do
    check "Typed view supplies title" (view.title == "Count")
  check "Hidden view serializes as null" (DisplayProtocol.viewToJson .hidden == Json.null)
  let hidden := CompiledView.render (Component.visibleWhen (.value false) Counter.form) 0
  check "Hidden rendering uses a typed hidden node" (hidden.view.isHidden)

def testFeedback : IO Unit := do
  let error : Feedback.Error := { message := "List error", targets := .locations [] [] }
  let global : Feedback.Error := { message := "Global", targets := .global }
  check "Root location messages deduplicate"
    (Feedback.messages [error, error, global] [] == some "List error")
  check "Global targets do not attach to fields"
    (Feedback.messages [global] [] == none)
  let path : Feedback.Location := [.field "items", .item 2, .constructor "circle"]
  let nested : Feedback.Error := { message := "Nested", targets := .locations path [] }
  check "Typed locations preserve item and constructor identity"
    (Feedback.messages [nested] path == some "Nested" &&
      Feedback.messages [nested] [.field "items", .item 1, .constructor "circle"] == none &&
      Feedback.messages [nested] [.field "items", .item 2, .constructor "rectangle"] == none)
  check "Location boundary round trip"
    ((FeedbackProtocol.locationFromJson (FeedbackProtocol.locationToJson path)).toOption == some path)
  let response := Json.mkObj [("error", Json.mkObj [("kind", toJson "replay"), ("message", toJson "Replay rejected")])]
  check "Replay message is preserved" ((FeedbackProtocol.serverError 400 response.compress).message == "Replay rejected")

def testTypedDispatch : IO Unit := do
  let editor := (CompiledView.render Counter.form 0).controls.find? (·.kind == .editor)
  let some editor := editor | throw (IO.userError "Missing counter editor")
  let invocation ← IO.ofExcept (editor.invoke (some (.text " 003 ")))
  check "Editor builds the typed action directly" (invocation.name == .replace)
  check "Editor applies the decoded natural" (invocation.apply 0 == 3)
  check "Editor requires an argument" (!(editor.invoke none).isOk)
  let button := (CompiledView.render Counter.form 0).controls.find? (·.kind == .button)
  let some button := button | throw (IO.userError "Missing counter button")
  let invocation ← IO.ofExcept (button.invoke none)
  check "Button builds the typed action directly" (invocation.name == .plusOne)
  check "Button applies its expression" (invocation.apply 5 == 6)
  check "Button rejects an argument" (!(button.invoke (some (.text ""))).isOk)

def run : IO Unit := do
  testFormatting
  testDisplay
  testTypedDispatch
  testFeedback
  let (store, opened) ← IO.ofExcept (execute {} (openRequest .counter))
  let handle ← IO.ofExcept (opened.getObjValAs? String "handle")
  let key := (toJson [toJson ([] : List Json), toJson "plusOne"]).compress
  let action := request "apply" handle [("key", toJson key)]
  let (updated, snapshot) ← IO.ofExcept (execute store action)
  let submission ← IO.ofExcept (snapshot.getObjVal? "submission")
  discard <| IO.ofExcept ((ComponentHistoryProtocol.verify Counter.form 0 submission).mapError toString)
  check "Compiled action changes value" ((← IO.ofExcept (submission.getObjValAs? String "value")) == "1")
  let (_, reset) ← IO.ofExcept (execute updated (request "reset" handle))
  check "Compiled reset restores initial value"
    ((← IO.ofExcept ((← IO.ofExcept (reset.getObjVal? "submission")).getObjValAs? String "value")) == "0")
  let (disposed, _) ← IO.ofExcept (execute updated (request "dispose" handle))
  check "Disposed handles reject actions" ((execute disposed action).isOk == false)
  let (reopened, next) ← IO.ofExcept (execute disposed (openRequest .counter))
  check "Handles are not reused" ((← IO.ofExcept (next.getObjValAs? String "handle")) != handle)
  check "Old handles stay invalid" ((execute reopened action).isOk == false)
  check "Failed actions are rejected" ((execute updated
    (request "apply" handle [("key", toJson "missing")])).isOk == false)
  check "Stale revisions are rejected" ((execute {} (openRequest .counter "stale")).isOk == false)
  check "Unknown operations are rejected" ((execute updated (request "unknown" handle)).isOk == false)
  check "Server-only checks stay on server" ((CompiledForms.clientErrors (Tests.ServerRefinements.even) 3).isEmpty)
  check "Client checks still run inside server refinements"
    (!(CompiledForms.clientErrors (Tests.ServerRefinements.even Tests.ServerRefinements.positive) 0).isEmpty)
  for selected in FinEnum.toList Example do
    let (_, result) ← IO.ofExcept (execute {} (openRequest selected))
    check "Compiled initialization returns a snapshot" ((result.getObjVal? "snapshot").isOk)
  let guarded := Component.disabledWhen (.value true) Counter.form
  let blocked := CompiledView.render guarded 0
  check "Disabled controls are rendered disabled" (blocked.controls.all (·.disabled))
  check "Disabled controls cannot be invoked" ((CompiledView.invocation guarded 0 ⟨key⟩ none).isOk == false)
  let hidden := Component.visibleWhen (.value false) Counter.form
  check "Hidden controls are omitted" ((CompiledView.render hidden 0).controls.isEmpty)
  check "Hidden controls cannot be invoked" ((CompiledView.invocation hidden 0 ⟨key⟩ none).isOk == false)
  IO.println "PASS: compiled model actions, replay, reset, disposal, guards, and server-only validation"

end Tests.CompiledForms
