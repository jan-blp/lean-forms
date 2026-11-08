module

public import Forms.ExampleForms.Person
public import Forms.Runtime.ModelProtocol

@[expose] public section
namespace Forms.Runtime.PersonProtocol
open Lean Forms.ExampleForms.Person

def name := "person"
abbrev State := ModelForm.State Person.Raw

def descriptor (revision : String) : Json :=
  toJson ({ form := name, revision, value := toJson initial } : Wire.CompiledDescriptor)

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
  let command ← ModelProtocol.commandFromWire request
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
