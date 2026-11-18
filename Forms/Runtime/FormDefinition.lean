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
  [decode : FromJson Raw]
  initial : Json
  openState (value : Json) (supply : Model.Supply) : Except String (State × ModelForm.Snapshot Raw)
  execute : State → ModelForm.Event Raw → Except String (State × ModelForm.Snapshot Raw)
  validate : Raw → Except Feedback.ServerError Unit

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
    if let some corrupt := Model.corruption? model value then throw corrupt.message
    let state := ModelForm.load form
      (ModelForm.openState (model := model) form value Model.Env.nil supply)
    pure (state, ModelForm.snapshot form state)
  execute state input := do
    let state ← ModelForm.execute (model := model) form state input
    pure (state, ModelForm.snapshot form state)
  validate value :=
    match Model.Validation.validate (model := model) value with
    | .ok _ => .ok ()
    | .error errors =>
      let errors := errors.map fun error =>
        ({ message := error.message, targets := error.targets.erase } : Feedback.ValidationError)
      match errors with
      | first :: rest => .error (.validation first rest)
      -- `Validation` may fail without errors.
      | [] => .error (.invalidRequest "The submission is invalid.")

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
  letI := form.definition.decode
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
