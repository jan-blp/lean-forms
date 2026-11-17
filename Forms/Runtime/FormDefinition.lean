module

public import Forms.Runtime.ModelProtocol
public import Forms.Model.Component.LocalState

@[expose] public section
namespace Forms.Runtime
open Lean

structure FormDefinition where
  State : Type
  Raw : Type
  [encode : ToJson Raw]
  initial : Json
  openState (value : Json) (supply : Model.Supply) : Except String (State × ModelForm.Snapshot Raw)
  execute : State → ModelForm.Event → Except String (State × ModelForm.Snapshot Raw)
  verify (name fingerprint : String) (submission : Json) : Except Json Unit

/-- Checked first, so a stale client gets a reload hint instead of a decode error. -/
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

def FormDefinition.ofModel
  {β : Type}
  (model : Type)
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  [ToJson (Model.Raw model)]
  [FromJson (Model.Raw model)]
  (form : Model.Component [] (Model.Raw model) β)
  (initial : Model.Raw model)
  : FormDefinition where
  State := ModelForm.State form
  Raw := Model.Raw model
  initial := toJson initial
  openState value supply := do
    let value ← fromJson? value
    if let some corrupt := (Model.errors (Model.Validation.validate (model := model) value)).find?
        (·.kind matches .corrupt) then
      throw corrupt.message
    let state := ModelForm.load form
      (ModelForm.openState (model := model) form value Model.Env.nil supply)
    pure (state, ModelForm.snapshot form state)
  execute state input := do
    let state ← ModelForm.execute (model := model) form state input
    pure (state, ModelForm.snapshot form state)
  verify name fingerprint json := do
    let value ← (decodeSubmission (Model.Raw model) name fingerprint json).mapError fun message =>
      Json.mkObj [("kind", toJson "request"), ("message", toJson message)]
    match Model.Validation.validate (model := model) value with
    | .ok _ => pure ()
    | .error errors =>
      let errors := errors.map ModelView.error
      throw (.mkObj [
        ("kind", toJson "validation"),
        ("message", toJson (Model.Diagnostic.summary errors)),
        ("errors", toJson (errors.map FeedbackProtocol.errorToJson))])

structure RegisteredForm where
  definition : FormDefinition
  submitUrl : String

structure FormInstance where
  execute : Wire.Event → Except String (FormInstance × Wire.Snapshot)

instance : Inhabited FormInstance := ⟨.mk fun _ => .error "Uninitialized form"⟩

def RegisteredForm.start (form : RegisteredForm) (name fingerprint : String) : Wire.FormStart :=
  { form := name, fingerprint, value := form.definition.initial }

def RegisteredForm.toWire
  (form : RegisteredForm)
  (name fingerprint : String)
  (snapshot : ModelForm.Snapshot form.definition.Raw)
  : Wire.Snapshot :=
  letI := form.definition.encode
  snapshot.toWire name fingerprint form.submitUrl

partial def RegisteredForm.instance
  (form : RegisteredForm)
  (name fingerprint : String)
  (state : form.definition.State)
  : FormInstance :=
  .mk fun message => do
    let input ← ModelForm.Event.fromWire message
    let (state, snapshot) ← form.definition.execute state input
    pure (form.instance name fingerprint state, form.toWire name fingerprint snapshot)

def RegisteredForm.open
  (form : RegisteredForm)
  (name fingerprint : String)
  (value : Json)
  (supply : Model.Supply)
  : Except String (FormInstance × Wire.Snapshot) := do
  let (state, snapshot) ← form.definition.openState value supply
  pure (form.instance name fingerprint state, form.toWire name fingerprint snapshot)

end Forms.Runtime
