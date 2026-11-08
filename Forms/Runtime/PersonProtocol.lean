module

public import Forms.ExampleForms.Person
public import Forms.Runtime.ModelForm
public import Forms.Runtime.InputProtocol

@[expose] public section
namespace Forms.Runtime.PersonProtocol
open Lean Forms.ExampleForms.Person

def name := "person"
abbrev State := ModelForm.State Person.Raw

def descriptor (revision : String) : Json :=
  toJson ({ form := name, revision, value := toJson initial } : Wire.CompiledDescriptor)

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

def submission (value : Person.Raw) : Json :=
  .mkObj [("form", toJson name), ("value", toJson value)]

def snapshot (state : State) (render := true) : Wire.FormSnapshot :=
  let snapshot := ModelForm.snapshot (model := Person) form state render
  { title := snapshot.view.title
    view := DisplayProtocol.layoutToWire (DisplayLayout.page snapshot.view snapshot.ui snapshot.actions
      (toJson snapshot.value).pretty)
    render := snapshot.render
    focus := snapshot.ui.focus.map (·.value)
    summary := snapshot.summary
    submissionBlocked := snapshot.submissionBlocked
    controls := snapshot.controls.map DisplayProtocol.controlToJson
    submission := submission snapshot.value
    errors := snapshot.errors.map FeedbackProtocol.errorToJson
    effects := if snapshot.ui.send then [{
      url := "/api/submit", method := .POST
      headers := { «Content-Type» := "application/json" }, body := (submission snapshot.value).compress }] else [] }

def execute (state : State) (request : Wire.FormRequest) : Except String (State × Wire.FormSnapshot) := do
  let command ← commandFromWire request
  let state ← ModelForm.execute (model := Person) form state command
  pure (state, snapshot state command.render)

def verifySubmission (json : Json) : Except Json Unit := do
  let value ← (do
    unless (← json.getObjValAs? String "form") == name do throw "Wrong form."
    fromJson? (α := Person.Raw) (← json.getObjVal? "value")).mapError fun message =>
      Json.mkObj [("kind", toJson "request"), ("message", toJson message)]
  match Person.validate value with
  | .ok _ => pure ()
  | .error errors =>
    let errors := errors.map ModelView.error
    throw (.mkObj [("kind", toJson "validation"), ("message", toJson (Feedback.summary errors)),
      ("errors", toJson (errors.map FeedbackProtocol.errorToJson))])

end Forms.Runtime.PersonProtocol
