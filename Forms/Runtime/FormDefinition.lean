module

public import Forms.Runtime.ModelProtocol
public import Forms.Model.Component.LocalState

@[expose] public section
namespace Forms.Runtime
open Lean

/-- A form's typed state transitions. -/
structure FormDefinition where
  State : Type
  Raw : Type
  [encode : ToJson Raw]
  /-- The raw value new forms start from. -/
  initial : Json
  /-- Decode the initial value and create the state and first snapshot. -/
  openState (value : Json) : Except String (State × ModelForm.Snapshot Raw)
  execute : State → ModelForm.Command → Except String (State × ModelForm.Snapshot Raw)
  /-- Checks a submission to the form registered as `name`, fingerprint first. -/
  verify (name fingerprint : String) (submission : Json) : Except Json Unit

/-- Checked first, so a stale client gets a reload hint instead of a decode error. -/
def decodeSubmission
  (raw : Type)
  [FromJson raw]
  (name fingerprint : String)
  (json : Json)
  : Except String raw := do
  unless (json.getObjValAs? String "fingerprint").toOption == some fingerprint do
    throw "This form is out of date. Reload the page."
  let submission ← fromJson? (α := Submission raw) json
  unless submission.form == name do throw "Wrong form."
  pure submission.value

/-- `model` rendered by `form`, starting from `initial`. -/
def FormDefinition.ofModel
  (model : Type)
  [FormModel model]
  [Model.Validation model]
  [ToJson (FormModel.Raw model)]
  [FromJson (FormModel.Raw model)]
  (form : Model.Component [] (FormModel.Raw model))
  (initial : FormModel.Raw model)
  : FormDefinition where
  State := ModelForm.State form
  Raw := FormModel.Raw model
  initial := toJson initial
  openState value := do
    let state := ModelForm.load form (ModelForm.openState form (← fromJson? value) Model.Env.nil)
    pure (state, ModelForm.snapshot (model := model) form state)
  execute state command := do
    let state ← ModelForm.execute (model := model) form state command
    pure (state, ModelForm.snapshot (model := model) form state)
  verify name fingerprint json := do
    let value ← (decodeSubmission (FormModel.Raw model) name fingerprint json).mapError fun message =>
      Json.mkObj [("kind", toJson "request"), ("message", toJson message)]
    match Model.Validation.validate (model := model) value with
    | .ok _ => pure ()
    | .error errors =>
      let errors := errors.map ModelView.error
      throw (.mkObj [
        ("kind", toJson "validation"),
        ("message", toJson (Feedback.summary errors)),
        ("errors", toJson (errors.map FeedbackProtocol.errorToJson))])

/-- A form definition and its application-specific submission endpoint. -/
structure RegisteredForm where
  definition : FormDefinition
  submitUrl : String

/-- An open form. -/
structure FormInstance where
  execute : Wire.Command → Except String (FormInstance × Wire.Snapshot)

instance : Inhabited FormInstance := ⟨.mk fun _ => .error "Uninitialized form"⟩

/-- The `FormStart` that opens a new `name` form. -/
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
  .mk fun request => do
    let command ← ModelForm.Command.fromWire request
    let (state, snapshot) ← form.definition.execute state command
    pure (form.instance name fingerprint state, form.toWire name fingerprint snapshot)

def RegisteredForm.open
  (form : RegisteredForm)
  (name fingerprint : String)
  (value : Json)
  : Except String (FormInstance × Wire.Snapshot) := do
  let (state, snapshot) ← form.definition.openState value
  pure (form.instance name fingerprint state, form.toWire name fingerprint snapshot)

end Forms.Runtime
