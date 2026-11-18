module

public import Forms.Runtime.FormDefinition

@[expose] public section
namespace Forms.Runtime
open Lean

/-- Kept out of the browser build. -/
structure ServerForm where
  form : RegisteredForm
  store : form.definition.Raw → form.definition.Raw

def ServerForm.plain (form : RegisteredForm) : ServerForm :=
  { form, store := id }

def decodeSubmission
  (α : Type)
  [FromJson α]
  (name fingerprint : String)
  (json : Json)
  : Except String α := do
  unless (json.getObjValAs? String "fingerprint").toOption == some fingerprint do
    throw "This form is out of date. Reload the page."
  let submission ← fromJson? (α := Submission α) json
  unless submission.form == name do throw "Wrong form."
  pure submission.value

def ServerForm.submit
  (server : ServerForm)
  (name fingerprint : String)
  (submission : Json)
  : Except Feedback.ServerError Json :=
  letI := server.form.definition.encode
  letI := server.form.definition.decode
  do
    let value ← (decodeSubmission server.form.definition.Raw name fingerprint submission).mapError
      .invalidRequest
    server.form.definition.validate value
    return toJson ({ value := server.store value } : Saved server.form.definition.Raw)

end Forms.Runtime
