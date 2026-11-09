module

public import Forms.ExampleForms.Person
public import Forms.Runtime.FormDefinition

@[expose] public section
namespace Forms.Runtime.PersonProtocol
open Lean Forms.ExampleForms

def name := "person"
abbrev State := ModelForm.State Person.Raw

def descriptor (fingerprint : String) : Json :=
  toJson ({ form := name, fingerprint, value := toJson Person.initial } : Wire.CompiledDescriptor)

def snapshot (fingerprint : String) (state : State) (render := true) : Wire.Snapshot :=
  let snapshot := ModelForm.snapshot (model := Person) Person.form state render
  snapshot.toWire name fingerprint "/api/submit"

def execute (fingerprint : String) (state : State) (request : Wire.Command) :
    Except String (State × Wire.Snapshot) := do
  let command ← ModelForm.Command.fromWire request
  let state ← ModelForm.execute (model := Person) Person.form state command
  pure (state, snapshot fingerprint state command.render)

def formDefinition : FormDefinition where
  State := State
  Raw := Person.Raw
  openState value := do
    let state := ModelForm.openState (← fromJson? value)
    pure (state, ModelForm.snapshot (model := Person) Person.form state)
  execute state command := do
    let state ← ModelForm.execute (model := Person) Person.form state command
    pure (state, ModelForm.snapshot (model := Person) Person.form state command.render)

/-- Checked first, so a stale client gets a reload hint instead of a decode error. -/
def verifySubmission (fingerprint : String) (json : Json) : Except Json Unit := do
  let value ← (do
    unless (json.getObjValAs? String "fingerprint").toOption == some fingerprint do
      throw "This form is out of date. Reload the page."
    let submission ← fromJson? (α := Submission Person.Raw) json
    unless submission.form == name do throw "Wrong form."
    pure submission.value).mapError fun message =>
      Json.mkObj [("kind", toJson "request"), ("message", toJson message)]
  match Person.validate value with
  | .ok _ => pure ()
  | .error errors =>
    let errors := errors.map ModelView.error
    throw (.mkObj [("kind", toJson "validation"), ("message", toJson (Feedback.summary errors)),
      ("errors", toJson (errors.map FeedbackProtocol.errorToJson))])

end Forms.Runtime.PersonProtocol
