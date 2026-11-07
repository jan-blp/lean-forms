module

public import Forms.Runtime.CompiledForms
public import Forms.Runtime.InputProtocol
public import Forms.Runtime.ComponentHistoryProtocol

@[expose] public section

namespace Forms.Runtime.CompiledFormsProtocol
open Lean Composition ExampleForms CompiledForms

def descriptor (revision : String) (selected : Example) : Json :=
  toJson ({ form := selected.name, revision, value := JsonProtocol.valueToJson selected.definition.initial } : Wire.CompiledDescriptor)

def openModel (request : Wire.CompiledDescriptor) : Except String ((selected : Example) × Model selected) := do
  let some selected := Example.ofName request.form | throw s!"Unknown compiled form: {request.form}"
  let initial ← JsonProtocol.valueFromJson selected.definition.ty request.value
  pure ⟨selected, CompiledForms.openModel selected initial⟩

def actionFromWire {selected : Example} (model : Model selected) (key : String) (argument : Json) : CompiledForms.Action selected :=
  { key := ⟨key⟩
    invocation := do
      let argument ← InputProtocol.argumentFromJson (if argument == Json.null then none else some argument)
      CompiledView.invocation selected.definition.component model.history.value ⟨key⟩ argument }

def eventFromWire {selected : Example} (model : Model selected) : Wire.FormEvent → Event selected
  | .draft key argument => .draft ⟨key⟩ argument
  | .apply key argument => .apply (actionFromWire model key argument)
  | .submit => .submit
  | .reset => .reset
  | .complete status body => .complete (if 200 ≤ status && status < 300 then .accepted
      else .rejected (FeedbackProtocol.serverError status body))
  | .failed message => .failed message

def commandFromWire {selected : Example} (model : Model selected) : Wire.FormRequest → Command selected
  | .event message => .event (eventFromWire model message)
  | .apply key argument => .apply (actionFromWire model key argument)
  | .reset => .reset
  | .validate => .validate
  | .serverError status body => .serverError (FeedbackProtocol.serverError status body)
  | .inspect => .inspect

def effectToWire {selected : Example} : Effect selected → Wire.HttpEffect
  | .submit history => {
      url := "/api/submit", method := .POST, headers := { «Content-Type» := "application/json" },
      body := (ComponentHistoryProtocol.encode history).compress }

def snapshotToWire {selected : Example} (snapshot : Snapshot selected) : Wire.FormSnapshot := {
  summary := snapshot.summary
  submissionBlocked := snapshot.submissionBlocked
  view := DisplayProtocol.layoutToWire (DisplayLayout.page snapshot.view snapshot.ui snapshot.history.actions.size
    (JsonProtocol.valueToJson snapshot.history.value).pretty)
  render := snapshot.render
  focus := snapshot.ui.focus.map (·.value)
  effects := snapshot.effects.map effectToWire
  controls := snapshot.controls.map DisplayProtocol.controlToJson
  title := snapshot.view.title
  submission := ComponentHistoryProtocol.encode snapshot.history
  errors := snapshot.errors.map FeedbackProtocol.errorToJson }

def snapshotToJson {selected : Example} (snapshot : Snapshot selected) : Json := toJson (snapshotToWire snapshot)

def responseToWire : Response → Wire.Response
  | .opened handle snapshot => .opened (toString handle.value) (snapshotToWire snapshot)
  | .updated snapshot => .updated (snapshotToWire snapshot)
  | .disposed => .disposed

def responseToJson (response : Response) : Json := toJson (responseToWire response)

def decodeHandle (text : String) : Except String Handle := do
  let some value := text.toNat? | throw "Invalid form handle"
  pure ⟨value⟩

def execute (revision : String) (store : Store) (json : Json) : Except String (Store × Response) := do
  match ← (fromJson? json : Except String Wire.Request) with
  | .open descriptor =>
    unless descriptor.revision == revision do
      throw "Compiled form version differs from the server. Rebuild Wasm and reload."
    let ⟨_, model⟩ ← openModel descriptor
    let (store, handle) := store.insert model
    pure (store, .opened handle (snapshot model))
  | .dispose text =>
    let handle ← decodeHandle text
    let _ ← store.find handle
    pure (store.dispose handle, .disposed)
  | .send text request =>
    let handle ← decodeHandle text
    let ⟨_, model⟩ ← store.find handle
    let command := commandFromWire model request
    let model ← CompiledForms.execute model command
    pure (store.replace handle model, .updated (snapshot model command.render))

def respond (revision : String) (store : Store) (text : String) : Store × String :=
  match Json.parse text >>= execute revision store with
  | .error error => (store, (toJson ({ ok := false, error } : Wire.Failure)).compress)
  | .ok (store, value) => (store, (toJson ({ ok := true, value := responseToWire value } : Wire.Success)).compress)

end Forms.Runtime.CompiledFormsProtocol
