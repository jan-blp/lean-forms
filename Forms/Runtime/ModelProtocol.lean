module

public import Forms.Runtime.ModelForm
public import Forms.Runtime.InputProtocol

@[expose] public section
namespace Forms.Runtime
open Lean

/-- A form's registered name, the fingerprint of the code that produced it, and submitted value. -/
structure Submission (raw : Type) where
  form : String
  fingerprint : String
  value : raw
  deriving ToJson, FromJson

def ModelForm.Snapshot.toWire {raw : Type} [ToJson raw] (snapshot : ModelForm.Snapshot raw)
    (formName fingerprint submitUrl : String) : Wire.Snapshot :=
  let submission := toJson ({ form := formName, fingerprint, value := snapshot.value } : Submission raw)
  { title := snapshot.view.title
    view := (DisplayLayout.page snapshot.view snapshot.ui snapshot.actions
      (toJson snapshot.value).pretty).toWire
    render := snapshot.render
    focus := snapshot.ui.focus.map (·.value)
    summary := snapshot.summary
    submissionBlocked := snapshot.submissionBlocked
    controls := snapshot.controls.map DisplayProtocol.controlToJson
    submission
    errors := snapshot.errors.map FeedbackProtocol.errorToJson
    effects := if snapshot.ui.send then [{
      url := submitUrl, method := .POST
      headers := { «Content-Type» := "application/json" }, body := submission.compress }] else [] }

def ModelForm.Event.fromWire : Wire.Event → Except String ModelForm.Event
  | .draft key value => .ok (.draft ⟨key⟩ value)
  | .apply key argument => do
    let argument ← InputProtocol.argumentFromJson (if argument == .null then none else some argument)
    pure (.apply ⟨key⟩ argument)
  | .submit => .ok .submit
  | .reset => .ok .reset
  | .complete status body => .ok (.complete (if 200 ≤ status && status < 300 then none
      else some (FeedbackProtocol.serverError status body)))
  | .failed message => .ok (.failed message)

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
