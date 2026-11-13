module

public import Forms.Runtime.ModelForm
public import Forms.Runtime.InputProtocol
public import Forms.Runtime.ReactView
public import Forms.Runtime.Wire

@[expose] public section
namespace Forms.Runtime
open Lean

/-- A form's registered name, the fingerprint of the code that produced it, and submitted value. -/
structure Submission (α : Type) where
  form : String
  fingerprint : String
  value : α
  deriving ToJson, FromJson

def fetchEffect (request : Model.HttpRequest) : Wire.Effect :=
  .fetch (toJson request).compress {
    url := request.url
    method := match request.method with
      | .get => .GET
      | .post => .POST
    headers := { «Content-Type» := "application/json" }
    body := request.body }

def fetchedRequest (id : String) : Except String Model.HttpRequest :=
  Json.parse id >>= fromJson?

def ModelForm.Snapshot.toWire
  {α : Type}
  [ToJson α]
  (snapshot : ModelForm.Snapshot α)
  (formName fingerprint submitUrl : String)
  : Wire.Snapshot :=
  let submission := toJson ({ form := formName, fingerprint, value := snapshot.value } : Submission α)
  let view := snapshot.view.toReactPage snapshot.ui (toJson snapshot.value).pretty
  { title := snapshot.view.title
    view
    draftFields := view.draftFields
    rejection := snapshot.ui.rejection
    summary := snapshot.summary
    submissionBlocked := snapshot.submissionBlocked
    controls := snapshot.controls.map DisplayProtocol.controlToJson
    submission
    errors := snapshot.errors.map FeedbackProtocol.errorToJson
    effects := snapshot.effects.map fun
      | .submit => .submit {
          url := submitUrl
          method := .POST
          headers := { «Content-Type» := "application/json" }
          body := some submission.compress }
      | .fetch request => fetchEffect request }

def ModelForm.Event.fromWire : Wire.Event → Except String ModelForm.Event
  | .apply key argument => do
    let argument ← InputProtocol.argumentFromJson (if argument == .null then none else some argument)
    pure (.apply ⟨key⟩ argument)
  | .submit => .ok .submit
  | .reset => .ok .reset
  | .submitted (.response status body) =>
    let rejection := if 200 ≤ status && status < 300 then none
      else some (FeedbackProtocol.serverError status body)
    .ok (.submitted (.ok rejection))
  | .submitted (.unreachable message) => .ok (.submitted (.error message))
  | .fetched id outcome => do
    let response := match outcome with
      | .response status body => if 200 ≤ status && status < 300 then Json.parse body
        else .error s!"The server responded with status {status}."
      | .unreachable message => .error message
    pure (.loaded (← fetchedRequest id) response)

end Forms.Runtime
