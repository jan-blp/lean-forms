module

public import Forms.Runtime.ModelView
public import Forms.Runtime.Interaction
public import Forms.Model.Requests

@[expose] public section
namespace Forms.Runtime.ModelForm

/-- A request the next snapshot asks the client to send. -/
inductive Effect where
  | submit
  | fetch (request : Model.HttpRequest)
  deriving BEq

structure State {Γ : Model.Context} {α β : Type} (form : Model.Component Γ α β) where
  /-- Reused until the model, context, cache, or private state changes. -/
  evaluation : ModelView.Evaluated Γ α form.LocalState β
  initial : α
  initialEnv : Model.Env Γ
  ui : Interaction.State
  serverFeedback : Option Feedback.ServerError
  /-- Effects of the last event, sent with its snapshot. -/
  outbox : List Effect

variable {Γ : Model.Context} {α β : Type} {form : Model.Component Γ α β}

@[reducible] def State.value (state : State form) : α := state.evaluation.value
@[reducible] def State.env (state : State form) : Model.Env Γ := state.evaluation.env
@[reducible] def State.cache (state : State form) : Model.HttpRequest.Cache := state.evaluation.cache
@[reducible] def State.locals (state : State form) : form.LocalState := state.evaluation.locals

def openState
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (value : α)
  (env : Model.Env Γ)
  (cache : Model.HttpRequest.Cache := {})
  : State form where
  evaluation := ModelView.evaluate form value cache env form.initialState
  initial := value
  initialEnv := env
  ui := .initial
  serverFeedback := none
  outbox := []

/-- Marks the requests `form` reads but has not loaded as loading, and queues them. -/
def load
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  : State form :=
  let missing := (state.evaluation.requests.filter (!state.cache.contains ·)).eraseDups
  if missing.isEmpty then state else
    let cache := missing.foldl (fun cache request => cache.insert request .loading) state.cache
    { state with
      evaluation := ModelView.evaluate form state.value cache state.env state.locals
      outbox := state.outbox ++ missing.map .fetch }

/-- Starts over from `initial`, keeping loaded responses; failed requests are retried. -/
def restart
  {Γ : Model.Context}
  {α β : Type}
  {form : Model.Component Γ α β}
  (state : State form)
  : State form :=
  let cache := state.cache.filter fun _ response => match response with
    | .failed _ => false
    | .loading => true
    | .loaded _ => true
  openState form state.initial state.initialEnv cache

inductive SubmitOutcome where
  | accepted
  | rejected (feedback : Feedback.ServerError)
  | unreachable (message : String)

-- Message from Ts to Lean (see `Wire.Event` for the serialized type)
inductive Event where
  | apply (key : ControlKey) (argument : Option Input)
  | submit
  | reset
  | submitted (outcome : SubmitOutcome)
  | loaded (request : Model.HttpRequest) (response : Except String Lean.Json)

def validationErrors
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (value : FormModel.Raw model)
  : List Feedback.Error :=
  (Model.errors (Model.Validation.validate (model := model) value)).map ModelView.error

-- Message from Lean to Ts (see `Wire.Snapshot` for the serialized type)
structure Snapshot (α : Type) where
  view : Display.View
  controls : List Display.Control
  value : α
  ui : Interaction.State
  errors : List Feedback.Error
  effects : List Effect

def snapshot {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  (form : Model.Component Γ (FormModel.Raw model) β)
  (state : State form)
  : Snapshot (FormModel.Raw model) :=
  let errors := validationErrors (model := model) state.value
  let visible := match state.serverFeedback with
    | some feedback => feedback.errors
    | none => errors
  let view := if visible.isEmpty then state.evaluation.view else state.evaluation.feedback visible
  { view, controls := view.controls, value := state.value,
    ui := state.ui, errors,
    effects := state.outbox }

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

def Rejection.ofAction : ModelView.ActionError → Rejection
  | .decode error => .ofDecode error
  | .invalid error => .stale (.invocation error)

/-- Checks a control and computes its update. -/
def validateAction
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  (key : ControlKey)
  (argument : Option Input)
  : Except Rejection (Model.ComponentUpdate Γ α form.LocalState) := do
  if state.ui.pending then throw (.stale .pending)
  (state.evaluation.applyKey key argument).mapError .ofAction

def applyUpdate
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  (updated : Model.ComponentUpdate Γ α form.LocalState)
  : State form :=
  { state with
    evaluation := ModelView.evaluate form updated.value state.cache updated.state updated.locals
    serverFeedback := none
    ui := { state.ui with notice := .info "", resultVisible := false } }

def apply
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  (key : ControlKey)
  (argument : Option Input)
  : Except Rejection (State form) := do
  return applyUpdate form state (← validateAction form state key argument)

def submit
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  {form : Model.Component Γ (FormModel.Raw model) β}
  (state : State form)
  : State form :=
  if state.ui.pending then state else
  let errors := validationErrors (model := model) state.value
  let state := { state with serverFeedback := none }
  if errors.isEmpty then
    { state with
      ui := { state.ui with pending := true, notice := .info "Submitting…" }
      outbox := state.outbox ++ [.submit] }
  else
    { state with ui := state.ui.announce (Feedback.summary errors) true }

def event {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  (form : Model.Component Γ (FormModel.Raw model) β)
  (state : State form)
  : Event → Except String (State form) := fun event => do
  let state := { state with ui := { state.ui with rejection := none } }
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
      { restart state with ui := { Interaction.State.initial with notice := .info "Started over." } })
  | .submitted outcome =>
    if !state.ui.pending then return state
    match outcome with
    | .accepted => pure { state with ui := { state.ui with
        pending := false, resultVisible := true, notice := .info "Submitted successfully." } }
    | .rejected feedback => pure { state with
        serverFeedback := some feedback
        ui := { (state.ui.announce feedback.message true) with pending := false } }
    | .unreachable message =>
      pure { state with ui := { (state.ui.announce message true) with pending := false } }
  | .loaded request response =>
    match state.cache[request]? with
    | some .loading =>
      let cached := match response with
        | .ok json => .loaded json
        | .error message => .failed message
      pure { state with evaluation := ModelView.evaluate form state.value (state.cache.insert request cached) state.env state.locals }
    | _ => pure state

/-- Handles `input`, then queues the requests the new state reads. -/
def execute {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  (form : Model.Component Γ (FormModel.Raw model) β)
  (state : State form)
  (input : Event)
  : Except String (State form) :=
  load form <$> event (model := model) form { state with outbox := [] } input

end Forms.Runtime.ModelForm
