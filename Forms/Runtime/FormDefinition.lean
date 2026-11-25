module

public import Forms.Runtime.ModelProtocol
public import Forms.Model.Component.LocalState
public import Forms.Model.Configuration

@[expose] public section
namespace Forms.Runtime
open Lean

structure OpenedForm (State Raw : Type) where
  state : State
  snapshot : ModelForm.Snapshot Raw
  /-- Describes the settings that were ignored. -/
  warnings : List String

structure FormDefinition where
  State : Type
  Raw : Type
  [encode : ToJson Raw]
  [decode : FromJson Raw]
  initial : Json
  openState (value : Json) (settings : Model.Settings) (supply : Model.Supply)
    : Except String (OpenedForm State Raw)
  execute : State → ModelForm.Event Raw → Except String (State × ModelForm.Snapshot Raw)
  validate : Raw → Except Feedback.ServerError Unit

def validateModel
  (model : Type)
  [FormModel model]
  [Model.Validation model]
  (value : Model.Raw model)
  : Except Feedback.ServerError Unit :=
  match Model.Validation.validate (model := model) value with
  | .ok _ => .ok ()
  | .error errors =>
    let errors := errors.map fun error =>
      ({ message := error.message, targets := error.targets.erase } : Feedback.ValidationError)
    match errors with
    | first :: rest => .error (.validation first rest)
    -- `Validation` may fail without errors.
    | [] => .error (.invalidRequest "The submission is invalid.")

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
  openState value settings supply := do
    let value ← fromJson? value
    let state := ModelForm.load form
      (ModelForm.openState (model := model) form value Model.Env.nil supply)
    let (_, warnings) := settings.resolve (K := Empty) nofun
    pure { state, snapshot := ModelForm.snapshot form state, warnings }
  execute state input := do
    let state ← ModelForm.execute (model := model) form state input
    pure (state, ModelForm.snapshot form state)
  validate := validateModel model

/-- A form whose fields follow the settings it is opened with. -/
def FormDefinition.ofConfigured
  (model : Type)
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  [ToJson (Model.Raw model)]
  [FromJson (Model.Raw model)]
  {K : Type}
  [Model.FieldKey K]
  [Model.FieldPaths (Model.Raw model) K]
  (form : Model.Configured [] (Model.Raw model) K)
  (initial : Model.Raw model)
  (wellKeyed : form.WellKeyed := by decide +kernel)
  : FormDefinition where
  State := (resolution : Model.Resolution K form.capabilities) ×
    ModelForm.State (form.build wellKeyed.2.1 resolution)
  Raw := Model.Raw model
  initial := toJson initial
  openState value settings supply := do
    let value ← fromJson? value
    let (resolution, warnings) := settings.resolve form.capabilities
    let component := form.build wellKeyed.2.1 resolution
    let value := form.applyFallbacks wellKeyed.2.1 resolution value
    let state := ModelForm.load component
      (ModelForm.openExcluding (model := model) component value Model.Env.nil supply
        (form.excluded resolution))
    pure { state := ⟨resolution, state⟩, snapshot := ModelForm.snapshot component state, warnings }
  execute
    | ⟨resolution, state⟩, input => do
      let component := form.build wellKeyed.2.1 resolution
      let state ← ModelForm.execute (model := model) component state input
      pure (⟨resolution, state⟩, ModelForm.snapshot component state)
  validate := validateModel model

structure RegisteredForm where
  definition : FormDefinition
  submitUrl : String

structure FormInstance where
  execute : Wire.Event → Except String (FormInstance × Wire.Snapshot)

instance : Inhabited FormInstance := ⟨.mk fun _ => .error "Uninitialized form"⟩

def RegisteredForm.start
  (form : RegisteredForm)
  (name fingerprint : String)
  (settings : Model.Settings)
  : Wire.FormStart :=
  { form := name, fingerprint, value := form.definition.initial, settings }

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

structure OpenedInstance where
  form : FormInstance
  snapshot : Wire.Snapshot
  /-- Describes the settings that were ignored. -/
  warnings : List String

def RegisteredForm.open
  (form : RegisteredForm)
  (name fingerprint : String)
  (value : Json)
  (settings : Model.Settings)
  (supply : Model.Supply)
  : Except String OpenedInstance := do
  let opened ← form.definition.openState value settings supply
  pure {
    form := form.instance name fingerprint opened.state
    snapshot := form.toWire name fingerprint opened.snapshot
    warnings := opened.warnings }

end Forms.Runtime
