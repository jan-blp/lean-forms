module

public import Forms.Runtime.ModelForm
public import Forms.Runtime.InputProtocol

@[expose] public section
namespace Forms.Runtime
open Lean

/-- A form's registered name and submitted value. -/
structure Submission (raw : Type) where
  form : String
  value : raw
  deriving ToJson, FromJson

def ModelForm.Snapshot.toWire {raw : Type} [ToJson raw] (snapshot : ModelForm.Snapshot raw)
    (formName : String) (submitUrl : String) : Wire.Snapshot :=
  let submission := toJson ({ form := formName, value := snapshot.value } : Submission raw)
  { title := snapshot.view.title
    view := DisplayProtocol.layoutToWire (DisplayLayout.page snapshot.view snapshot.ui snapshot.actions
      (toJson snapshot.value).pretty)
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

namespace ModelProtocol

def eventFromWire : Wire.FormEvent → Except String ModelForm.Event
  | .draft key value => .ok (.draft ⟨key⟩ value)
  | .apply key argument => do
    let argument ← InputProtocol.argumentFromJson (if argument == .null then none else some argument)
    pure (.apply ⟨key⟩ argument)
  | .submit => .ok .submit
  | .reset => .ok .reset
  | .complete status body => .ok (.complete (if 200 ≤ status && status < 300 then none
      else some (FeedbackProtocol.serverError status body)))
  | .failed message => .ok (.failed message)

def commandFromWire : Wire.FormRequest → Except String ModelForm.Command
  | .event message => ModelForm.Command.event <$> eventFromWire message
  | .apply key argument => do
    let argument ← InputProtocol.argumentFromJson (if argument == .null then none else some argument)
    pure (.apply ⟨key⟩ argument)
  | .reset => .ok .reset
  | .validate => .ok .validate
  | .inspect => .ok .inspect
  | .serverError status body => .ok (.serverError (FeedbackProtocol.serverError status body))

end ModelProtocol
end Forms.Runtime
