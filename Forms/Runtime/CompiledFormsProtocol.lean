module

public import Forms.Runtime.CompiledForms
public import Forms.Runtime.InputProtocol
public import Forms.Runtime.ComponentHistoryProtocol

@[expose] public section

namespace Forms.Runtime.CompiledFormsProtocol
open Lean Composition ExampleForms CompiledForms

def descriptor (revision : String) (selected : Example) : Json :=
  Json.mkObj [("form", toJson selected.name), ("revision", toJson revision),
    ("value", JsonProtocol.valueToJson selected.definition.initial)]

def openModel (request : Json) : Except String ((selected : Example) × Model selected) := do
  let name ← request.getObjValAs? String "form"
  let some selected := Example.ofName name | throw s!"Unknown compiled form: {name}"
  let initial ← JsonProtocol.valueFromJson selected.definition.ty (← request.getObjVal? "value")
  pure ⟨selected, CompiledForms.openModel selected initial⟩

def actionFromJson {selected : Example} (model : Model selected) (request : Json) : Except String (CompiledForms.Action selected) := do
  let key := ControlKey.mk (← request.getObjValAs? String "key")
  pure { key
         invocation := do
           let argument ← InputProtocol.argumentFromJson (request.getObjVal? "argument").toOption
           CompiledView.invocation selected.definition.component model.history.value key argument }

def eventFromJson {selected : Example} (model : Model selected) (request : Json) : Except String (Event selected) := do
  match ← request.getObjValAs? String "event" with
  | "draft" => pure (.draft ⟨← request.getObjValAs? String "key"⟩ (← request.getObjValAs? String "argument"))
  | "apply" => pure (.apply (← actionFromJson model request))
  | "submit" => pure .submit
  | "reset" => pure .reset
  | "complete" =>
    let status ← request.getObjValAs? Nat "status"
    if 200 ≤ status && status < 300 then pure (.complete .accepted)
    else pure (.complete (.rejected (FeedbackProtocol.serverError status (← request.getObjValAs? String "body"))))
  | "failed" => pure (.failed (← request.getObjValAs? String "message"))
  | name => throw s!"Unknown UI event: {name}"

def commandFromJson {selected : Example} (model : Model selected) (operation : String) (request : Json) :
    Except String (Command selected) := do
  match operation with
  | "event" => pure (.event (← eventFromJson model request))
  | "apply" => pure (.apply (← actionFromJson model request))
  | "reset" => pure .reset
  | "validate" => pure .validate
  | "serverError" => pure (.serverError (FeedbackProtocol.serverError
      (← request.getObjValAs? Nat "status") (← request.getObjValAs? String "body")))
  | "inspect" => pure .inspect
  | operation => throw s!"Unknown form operation: {operation}"

def effectToJson {selected : Example} : Effect selected → Json
  | .submit history => Json.mkObj [
      ("url", toJson "/api/submit"), ("method", toJson "POST"),
      ("headers", Json.mkObj [("Content-Type", toJson "application/json")]),
      ("body", toJson (ComponentHistoryProtocol.encode history).compress)]

def snapshotToJson {selected : Example} (snapshot : Snapshot selected) : Json :=
  Json.mkObj [
    ("summary", toJson snapshot.summary), ("submissionBlocked", toJson snapshot.submissionBlocked),
    ("view", DisplayProtocol.layoutToJson (DisplayLayout.page snapshot.view snapshot.ui snapshot.history.actions.size
      (JsonProtocol.valueToJson snapshot.history.value).pretty)),
    ("render", toJson snapshot.render), ("focus", toJson (snapshot.ui.focus.map (·.value))),
    ("effects", toJson (snapshot.effects.map effectToJson)),
    ("controls", toJson (snapshot.controls.map DisplayProtocol.controlToJson)),
    ("title", toJson snapshot.view.title), ("submission", ComponentHistoryProtocol.encode snapshot.history),
    ("errors", toJson (snapshot.errors.map FeedbackProtocol.errorToJson))]

def responseToJson : Response → Json
  | .opened handle snapshot => Json.mkObj [("handle", toJson (toString handle.value)), ("snapshot", snapshotToJson snapshot)]
  | .updated snapshot => snapshotToJson snapshot
  | .disposed => Json.null

def handleFromJson (request : Json) : Except String Handle := do
  let text ← request.getObjValAs? String "handle"
  let some value := text.toNat? | throw "Invalid form handle"
  pure ⟨value⟩

def execute (revision : String) (store : Store) (request : Json) : Except String (Store × Response) := do
  let operation ← request.getObjValAs? String "operation"
  if operation == "open" then
    let expected ← request.getObjValAs? String "revision"
    unless expected == revision do
      throw "Compiled form version differs from the server. Rebuild Wasm and reload."
    let ⟨_, model⟩ ← openModel request
    let (store, handle) := store.insert model
    pure (store, .opened handle (snapshot model))
  else
    let handle ← handleFromJson request
    let ⟨_, model⟩ ← store.find handle
    if operation == "dispose" then
      pure (store.dispose handle, .disposed)
    else
      let command ← commandFromJson model operation request
      let model ← CompiledForms.execute model command
      pure (store.replace handle model, .updated (snapshot model command.render))

def respond (revision : String) (store : Store) (text : String) : Store × String :=
  match Json.parse text >>= execute revision store with
  | .error error => (store, (Json.mkObj [("ok", toJson false), ("error", toJson error)]).compress)
  | .ok (store, value) => (store, (Json.mkObj [("ok", toJson true), ("value", responseToJson value)]).compress)

end Forms.Runtime.CompiledFormsProtocol
