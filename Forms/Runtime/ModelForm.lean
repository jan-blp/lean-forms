module

public import Forms.Runtime.ModelView
public import Forms.Runtime.Interaction

@[expose] public section
namespace Forms.Runtime.ModelForm

structure State (raw : Type) where
  initial : raw
  value : raw
  ui : Interaction.State
  validationStarted : Bool
  serverFeedback : Option Feedback.ServerError

def openState {raw : Type} (value : raw) : State raw where
  initial := value
  value
  ui := .initial
  validationStarted := false
  serverFeedback := none

inductive Event where
  | apply (key : ControlKey) (argument : Option Input)
  | submit
  | reset
  | complete (error : Option Feedback.ServerError)
  | failed (message : String)

inductive Command where
  | event (event : Event)
  | apply (key : ControlKey) (argument : Option Input)
  | validate
  | reset
  | inspect
  | serverError (error : Feedback.ServerError)

def validationErrors
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (value : FormModel.Raw model)
  : List Feedback.Error :=
  (Model.errors (Model.Validation.validate (model := model) value)).map ModelView.error

structure Snapshot (raw : Type) where
  view : Display.View
  controls : List Display.Control
  value : raw
  ui : Interaction.State
  errors : List Feedback.Error
  summary : String
  submissionBlocked : Bool

def snapshot
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (form : Model.Component (FormModel.Raw model))
  (state : State (FormModel.Raw model))
  : Snapshot (FormModel.Raw model) :=
  let errors := validationErrors (model := model) state.value
  let visible := match state.serverFeedback with
    | some feedback => feedback.errors
    | none => if state.validationStarted then errors else []
  let rendered := ModelView.render form state.value visible
  { view := rendered.view, controls := rendered.controls, value := state.value,
    ui := state.ui, errors,
    summary := state.serverFeedback.map (·.message) |>.getD (Feedback.summary visible),
    submissionBlocked := !visible.isEmpty }

inductive StaleError where
  | pending
  | invocation (error : Model.InvocationError)
  deriving DecidableEq, Repr

instance : ToString StaleError where
  toString
    | .pending => "Submission is in progress."
    | .invocation error => toString error

/-- Why an action was not applied. -/
inductive Rejection where
  | input (message : String)
  | stale (error : StaleError)
  | clientBug (error : ClientBug)
  deriving DecidableEq, Repr

instance : ToString Rejection where
  toString
    | .input message => message
    | .stale error => toString error
    | .clientBug error => toString error

def Rejection.ofDecode : DecodeError → Rejection
  | .input message => .input message
  | .clientBug error => .clientBug error

/-- The checked invocation that `key` and `argument` name. -/
def validateAction
  {raw : Type}
  (form : Model.Component raw)
  (state : State raw)
  (key : ControlKey)
  (argument : Option Input)
  : Except Rejection (form.ValidInvocation state.value) := do
  if state.ui.pending then throw (.stale .pending)
  let invocation ← (ModelView.decodeKey form key argument).mapError .ofDecode
  (form.validate state.value invocation).mapError fun error => .stale (.invocation error)

def applyValid
  {raw : Type}
  (form : Model.Component raw)
  (state : State raw)
  (invocation : form.ValidInvocation state.value)
  : State raw :=
  { state with
    value := form.applyValid state.value invocation
    serverFeedback := none
    ui := { state.ui with notice := .info "", resultVisible := false } }

def apply
  {raw : Type}
  (form : Model.Component raw)
  (state : State raw)
  (key : ControlKey)
  (argument : Option Input)
  : Except Rejection (State raw) := do
  return applyValid form state (← validateAction form state key argument)

def submit
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (state : State (FormModel.Raw model))
  : State (FormModel.Raw model) :=
  if state.ui.pending then state else
  let errors := validationErrors (model := model) state.value
  let ui := if errors.isEmpty then { state.ui with submission := .requested, notice := .info "Submitting…" }
    else state.ui.announce (Feedback.summary errors) true
  { state with ui, validationStarted := true, serverFeedback := none }

def event
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (form : Model.Component (FormModel.Raw model))
  (state : State (FormModel.Raw model))
  : Event → Except String (State (FormModel.Raw model)) := fun event => do
  let state := { state with ui := { state.ui.acknowledge with rejection := none } }
  match event with
  | .apply key argument =>
    match apply form state key argument with
    | .ok state => pure state
    | .error (.clientBug error) => throw (toString error)
    | .error rejection =>
      let message := toString rejection
      let ui := if state.ui.pending then state.ui else state.ui.announce message true
      pure { state with ui := { ui with rejection := some message } }
  | .submit => pure (submit (model := model) state)
  | .reset => pure (if state.ui.pending then state else
      { (openState state.initial) with ui := { Interaction.State.initial with notice := .info "Started over." } })
  | .complete error =>
    if !state.ui.pending then return state
    match error with
    | none => pure { state with ui := { state.ui with
        submission := .idle, resultVisible := true, notice := .info "Submitted successfully." } }
    | some feedback => pure { state with
        serverFeedback := some feedback
        ui := { (state.ui.announce feedback.message true) with submission := .idle } }
  | .failed message => pure (if state.ui.pending then
      { state with ui := { (state.ui.announce message true) with submission := .idle } } else state)

def execute
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (form : Model.Component (FormModel.Raw model))
  (state : State (FormModel.Raw model))
  : Command → Except String (State (FormModel.Raw model))
  | .event input => event (model := model) form state input
  | .apply key argument => (apply form state key argument).mapError toString
  | .validate => .ok { state with validationStarted := true, serverFeedback := none }
  | .reset => if state.ui.pending then .error "Submission is in progress." else .ok (openState state.initial)
  | .serverError error => .ok { state with serverFeedback := some error }
  | .inspect => .ok state

end Forms.Runtime.ModelForm
