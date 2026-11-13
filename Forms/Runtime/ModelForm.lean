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

structure State {Γ : Model.Context} {α : Type} (form : Model.Component Γ α) where
  locals : form.LocalState
  initial : α
  initialEnv : Model.Env Γ
  env : Model.Env Γ
  value : α
  ui : Interaction.State
  serverFeedback : Option Feedback.ServerError
  cache : Model.HttpRequest.Cache
  /-- Effects of the last event, sent with its snapshot. -/
  outbox : List Effect

def openState
  {Γ : Model.Context}
  {α : Type}
  (form : Model.Component Γ α)
  (value : α)
  (env : Model.Env Γ)
  : State form where
  locals := form.initialState
  initial := value
  initialEnv := env
  env
  value
  ui := .initial
  serverFeedback := none
  cache := {}
  outbox := []

/-- Marks the requests `form` reads but has not loaded as loading, and queues them. -/
def load
  {Γ : Model.Context}
  {α : Type}
  (form : Model.Component Γ α)
  (state : State form)
  : State form :=
  let locals := form.normalize state.cache state.value state.env state.locals
  let missing := ((form.requests state.cache state.value state.env locals).filter (!state.cache.contains ·)).eraseDups
  { state with
    locals
    cache := missing.foldl (fun cache request => cache.insert request .loading) state.cache
    outbox := state.outbox ++ missing.map .fetch }

/-- Starts over from `initial`, keeping loaded responses; failed requests are retried. -/
def restart
  {Γ : Model.Context}
  {α : Type}
  {form : Model.Component Γ α}
  (state : State form)
  : State form :=
  { openState form state.initial state.initialEnv with
    cache := state.cache.filter fun _ response => match response with
      | .failed _ => false
      | .loading => true
      | .loaded _ => true }

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

-- Message from Lean to Ts (see Wire.Snapshot for serialized type)
structure Snapshot (α : Type) where
  view : Display.View
  controls : List Display.Control
  value : α
  ui : Interaction.State
  errors : List Feedback.Error
  summary : String
  submissionBlocked : Bool
  effects : List Effect

def snapshot {Γ : Model.Context}
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (form : Model.Component Γ (FormModel.Raw model))
  (state : State form)
  : Snapshot (FormModel.Raw model) :=
  let errors := validationErrors (model := model) state.value
  let visible := match state.serverFeedback with
    | some feedback => feedback.errors
    | none => errors
  let rendered := ModelView.render form state.value state.cache visible state.env state.locals
  { view := rendered.view, controls := rendered.controls, value := state.value,
    ui := state.ui, errors,
    summary := state.serverFeedback.map (·.message) |>.getD (Feedback.summary visible),
    submissionBlocked := !visible.isEmpty
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

/-- The checked invocation that `key` and `argument` name. -/
def validateAction
  {Γ : Model.Context}
  {α : Type}
  (form : Model.Component Γ α)
  (state : State form)
  (key : ControlKey)
  (argument : Option Input)
  : Except Rejection (form.ValidInvocation state.cache state.value state.env state.locals) := do
  if state.ui.pending then throw (.stale .pending)
  (ModelView.decodeKey form state.cache state.value key argument state.env state.locals).mapError .ofAction

def applyValid
  {Γ : Model.Context}
  {α : Type}
  (form : Model.Component Γ α)
  (state : State form)
  (invocation : form.ValidInvocation state.cache state.value state.env state.locals)
  : State form :=
  let updated := form.applyValid state.cache state.value state.env state.locals invocation
  { state with
    value := updated.value
    locals := updated.locals
    env := updated.state
    serverFeedback := none
    ui := { state.ui with notice := .info "", resultVisible := false } }

def apply
  {Γ : Model.Context}
  {α : Type}
  (form : Model.Component Γ α)
  (state : State form)
  (key : ControlKey)
  (argument : Option Input)
  : Except Rejection (State form) := do
  return applyValid form state (← validateAction form state key argument)

def submit
  {Γ : Model.Context}
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  {form : Model.Component Γ (FormModel.Raw model)}
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
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (form : Model.Component Γ (FormModel.Raw model))
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
      pure { state with cache := state.cache.insert request cached }
    | _ => pure state

/-- Handles `input`, then queues the requests the new state reads. -/
def execute {Γ : Model.Context}
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (form : Model.Component Γ (FormModel.Raw model))
  (state : State form)
  (input : Event)
  : Except String (State form) :=
  load form <$> event (model := model) form { state with outbox := [] } input

end Forms.Runtime.ModelForm
