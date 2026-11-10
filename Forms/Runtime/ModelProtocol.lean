module

public import Forms.Runtime.ModelForm
public import Forms.Runtime.InputProtocol
public import Forms.Runtime.ReactView
public import Forms.Runtime.Wire

@[expose] public section
namespace Forms.Runtime
open Lean

/-- A form's registered name, the fingerprint of the code that produced it, and submitted value. -/
structure Submission (raw : Type) where
  form : String
  fingerprint : String
  value : raw
  deriving ToJson, FromJson

def fetchEffect (request : Model.HttpRequest) : Wire.HttpEffect where
  url := request.url
  method := match request.method with
    | .get => .GET
    | .post => .POST
  headers := { «Content-Type» := "application/json" }
  body := request.body
  id := some (toJson request).compress

def fetchedRequest (id : String) : Except String Model.HttpRequest :=
  Json.parse id >>= fromJson?

def ModelForm.Snapshot.toWire
  {raw : Type}
  [ToJson raw]
  (snapshot : ModelForm.Snapshot raw)
  (formName fingerprint submitUrl : String)
  : Wire.Snapshot :=
  let submission := toJson ({ form := formName, fingerprint, value := snapshot.value } : Submission raw)
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
    effects :=
      let submit : List Wire.HttpEffect := if snapshot.ui.send then [{
        url := submitUrl, method := .POST
        headers := { «Content-Type» := "application/json" }, body := some submission.compress, id := none }]
        else []
      submit ++ snapshot.fetches.map fetchEffect }

def ModelForm.Event.fromWire : Wire.Event → Except String ModelForm.Event
  | .apply key argument => do
    let argument ← InputProtocol.argumentFromJson (if argument == .null then none else some argument)
    pure (.apply ⟨key⟩ argument)
  | .submit => .ok .submit
  | .reset => .ok .reset
  | .complete status body => .ok (.complete (if 200 ≤ status && status < 300 then none
      else some (FeedbackProtocol.serverError status body)))
  | .failed message => .ok (.failed message)
  | .fetched id status body => do
    let response := if 200 ≤ status && status < 300 then Json.parse body
      else .error s!"The server responded with status {status}."
    pure (.loaded (← fetchedRequest id) response)
  | .unreachable id message => do pure (.loaded (← fetchedRequest id) (.error message))

def ModelForm.Command.fromWire : Wire.Command → Except String ModelForm.Command
  | .event message => ModelForm.Command.event <$> ModelForm.Event.fromWire message
  | .apply key argument => do
    let argument ← InputProtocol.argumentFromJson (if argument == .null then none else some argument)
    pure (.apply ⟨key⟩ argument)
  | .reset => .ok .reset
  | .validate => .ok .validate
  | .inspect => .ok .inspect
  | .serverError status body => .ok (.serverError (FeedbackProtocol.serverError status body))

end Forms.Runtime
