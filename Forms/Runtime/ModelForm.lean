module

public import Forms.Runtime.ModelView
public import Forms.Runtime.Feedback
public import Forms.Runtime.Interaction
public import Forms.Model.Requests

@[expose] public section
namespace Forms.Runtime.ModelForm

inductive Effect where
  | submit
  | fetch (request : Model.HttpRequest)
  | focus (key : ControlKey)
  deriving BEq

/-- Whether `view` can still act on `effect`: a focus needs its control to be editable. -/
def Effect.applies (view : Display.View) : Effect → Bool
  | .submit => true
  | .fetch _ => true
  | .focus key => view.controls.any fun control => control.key == key && control.editable

/-- An error about a control's text that cannot enter the model, e.g. "abc" in a natural field;
dropped when the control commits or leaves the view. -/
structure DraftDiagnostic where
  control : ControlKey
  diagnostic : Model.Diagnostic
  deriving BEq

structure State {Γ : Model.Context} {α β : Type} (form : Model.Component Γ α β) where
  /-- Reused until the model, context, cache, or private state changes. -/
  evaluation : ModelView.Evaluated Γ α form.LocalState β
  initial : α
  initialEnv : Model.Env Γ
  ui : Interaction.State
  serverFeedback : Option Feedback.ServerError
  outbox : List Effect
  validationDiagnostics : List Model.Diagnostic
  reportDiagnostics : List Model.Diagnostic
  supply : Model.Supply
  draftDiagnostics : List DraftDiagnostic := []

variable {Γ : Model.Context} {α β : Type} {form : Model.Component Γ α β}

@[reducible] def State.value (state : State form) : α := state.evaluation.value
@[reducible] def State.env (state : State form) : Model.Env Γ := state.evaluation.env
@[reducible] def State.cache (state : State form) : Model.HttpRequest.Cache := state.evaluation.cache
@[reducible] def State.locals (state : State form) : form.LocalState := state.evaluation.locals

def validationErrors
  {model : Type}
  [FormModel model]
  [Model.Validation model]
  (value : Model.Raw model)
  : List Model.Diagnostic :=
  (Model.errors (Model.Validation.validate (model := model) value)).map ModelView.error

def reports
  {model : Type}
  [FormModel model]
  [Model.Reports model]
  (value : Model.Raw model)
  (checked : Bool)
  : List Model.Diagnostic :=
  (Model.Reports.reports (model := model) value).map (ModelView.report checked)

/-- The server's checks describe the document last opened or saved. -/
def checked
  {model : Type}
  [FormModel model]
  [Lean.ToJson (Model.Raw model)]
  (initial value : Model.Raw model)
  : Bool :=
  Lean.toJson value == Lean.toJson initial

def openState
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  (form : Model.Component Γ (Model.Raw model) β)
  (value : Model.Raw model)
  (env : Model.Env Γ)
  (supply : Model.Supply)
  (cache : Model.HttpRequest.Cache := {})
  : State form :=
  let validationDiagnostics := validationErrors (model := model) value
  let reportDiagnostics := reports (model := model) value true
  { evaluation := ModelView.evaluate form value cache env form.initialState
      (validationDiagnostics ++ reportDiagnostics)
    initial := value
    initialEnv := env
    ui := .initial
    serverFeedback := none
    outbox := []
    validationDiagnostics
    reportDiagnostics
    supply }

def refresh
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  : State form :=
  let diagnostics := state.draftDiagnostics.map (·.diagnostic) ++
    (state.serverFeedback.map (·.errors)).getD state.validationDiagnostics ++
    state.reportDiagnostics
  if diagnostics == state.evaluation.diagnostics then state else
    { state with
      evaluation := ModelView.evaluate form state.value state.cache state.env state.locals
        diagnostics }

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
    let evaluation := ModelView.evaluate form state.value cache state.env state.locals
      state.evaluation.diagnostics
    let outbox := state.outbox.filter (·.applies evaluation.view)
    { state with
      evaluation
      outbox := outbox ++ missing.map .fetch }

/-- Starts over from `initial`, keeping loaded responses; failed requests are retried. -/
def restart
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  {form : Model.Component Γ (Model.Raw model) β}
  (state : State form)
  : State form :=
  let cache := state.cache.filter fun _ response => match response with
    | .failed _ => false
    | .loading => true
    | .loaded _ => true
  openState (model := model) form state.initial state.initialEnv state.supply cache

inductive SubmitOutcome (α : Type) where
  /-- `saved` is the document the server stored. -/
  | accepted (saved : α)
  | rejected (feedback : Feedback.ServerError)
  | unreachable (message : String)

-- Message from Ts to Lean (see `Wire.Event` for the serialized type)
inductive Event (α : Type) where
  | apply (key : ControlKey) (argument : Option Input)
  | draft (key : ControlKey) (message : Option String)
  | submit
  | reset
  | submitted (outcome : SubmitOutcome α)
  | loaded (request : Model.HttpRequest) (response : Except String Lean.Json)

-- Message from Lean to Ts (see `Wire.Snapshot` for the serialized type)
structure Snapshot (α : Type) where
  view : Display.View
  controls : List Display.Control
  value : α
  ui : Interaction.State
  errors : List Model.Diagnostic
  effects : List Effect

def snapshot
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  : Snapshot α :=
  { view := state.evaluation.view
    controls := state.evaluation.view.controls
    value := state.value
    ui := state.ui
    errors := state.validationDiagnostics
    effects := state.outbox }

inductive StaleError where
  | pending
  | invocation (error : Model.InvocationError)
  deriving DecidableEq, Repr

instance : ToString StaleError where
  toString
    | .pending => "Submission is in progress."
    | .invocation error => toString error

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

def validateAction
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  (key : ControlKey)
  (argument : Option Input)
  : StateT Model.Supply (Except Rejection) (Model.ComponentUpdate Γ α form.LocalState) :=
  fun supply => do
    if state.ui.pending then throw (.stale .pending)
    state.evaluation.applyKey key argument |>.run supply |>.mapError .ofAction

def applyUpdate
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  [Lean.ToJson (Model.Raw model)]
  (form : Model.Component Γ (Model.Raw model) β)
  (state : State form)
  (updated : Model.ComponentUpdate Γ (Model.Raw model) form.LocalState)
  : State form :=
  let validationDiagnostics := validationErrors (model := model) updated.value
  let reportDiagnostics :=
    reports (model := model) updated.value (checked (model := model) state.initial updated.value)
  let diagnostics := state.draftDiagnostics.map (·.diagnostic) ++ validationDiagnostics ++
    reportDiagnostics
  let evaluation := ModelView.evaluate form updated.value state.cache updated.state updated.locals
    diagnostics
  let focus := updated.visit.bind (evaluation.view.resolve ·.locations)
  { state with
    evaluation
    validationDiagnostics
    reportDiagnostics
    serverFeedback := none
    outbox := state.outbox ++ focus.toList.map .focus
    ui := { state.ui with notice := .info "", resultVisible := false } }

def apply
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  [Lean.ToJson (Model.Raw model)]
  (form : Model.Component Γ (Model.Raw model) β)
  (state : State form)
  (key : ControlKey)
  (argument : Option Input)
  : Except Rejection (State form) := do
  let (updated, supply) ← (validateAction form state key argument).run state.supply
  let state := { state with
    supply
    draftDiagnostics := state.draftDiagnostics.filter (·.control != key) }
  let state := applyUpdate (model := model) form state updated
  let drafts := state.draftDiagnostics.filter fun draft =>
    state.evaluation.view.controls.any (·.key == draft.control)
  return refresh form { state with draftDiagnostics := drafts }

def submit
  {Γ : Model.Context}
  {α β : Type}
  {form : Model.Component Γ α β}
  (state : State form)
  : State form :=
  if state.ui.pending then state else
  let errors := state.validationDiagnostics
  let state := refresh form { state with serverFeedback := none }
  if errors.isEmpty && state.draftDiagnostics.isEmpty then
    { state with
      ui := { state.ui with pending := true, notice := .info "Submitting…" }
      outbox := state.outbox ++ [.submit] }
  else
    let diagnostics := state.draftDiagnostics.map (·.diagnostic) ++ errors
    let focus := state.evaluation.view.resolveFirst (diagnostics.map (·.locations))
    { state with
      ui := state.ui.announce (Model.Diagnostic.summary diagnostics) true
      outbox := state.outbox ++ focus.toList.map .focus }

def event {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  [Lean.ToJson (Model.Raw model)]
  (form : Model.Component Γ (Model.Raw model) β)
  (state : State form)
  : Event (Model.Raw model) → Except String (State form) := fun event => do
  let state := { state with ui := { state.ui with rejection := none } }
  match event with
  | .apply key argument =>
    match apply (model := model) form state key argument with
    | .ok state => pure state
    | .error rejection =>
      let message := toString rejection
      let ui := if state.ui.pending then state.ui else state.ui.announce message true
      let diagnostics ← match rejection with
        | .clientBug error => throw (toString error)
        | .input _ =>
          let control := if argument.any Input.typed
            then state.evaluation.view.controls.find? (·.key == key) else none
          pure <| match control with
          | none => state.draftDiagnostics
          | some control =>
            { control := key
              diagnostic :=
                { kind := .error, message, targets := .locations control.location [] } } ::
              state.draftDiagnostics.filter (·.control != key)
        | .stale _ => pure state.draftDiagnostics
      pure (refresh form { state with
        draftDiagnostics := diagnostics
        ui := { ui with rejection := some message } })
  | .draft key message =>
    if state.ui.pending then return state
    let some control := state.evaluation.view.controls.find? (·.key == key) | return state
    unless control.acceptsDrafts do return state
    let diagnostics := state.draftDiagnostics.filter (·.control != key)
    let diagnostics := match message with
      | none => diagnostics
      | some message =>
        { control := key
          diagnostic := { kind := .error, message, targets := .locations control.location [] } } ::
          diagnostics
    pure (refresh form { state with draftDiagnostics := diagnostics })
  | .submit => pure (submit state)
  | .reset => pure (if state.ui.pending then state else
      { restart (model := model) state with
        ui := { Interaction.State.initial with notice := .info "Started over." } })
  | .submitted outcome =>
    if !state.ui.pending then return state
    let unreachable (message : String) :=
      { state with ui := { (state.ui.announce message true) with pending := false } }
    match outcome with
    | .accepted saved =>
      if (Model.corruption? model saved).isSome
      then return unreachable "Your form was saved, but an internal error occurred. Please contact BLP."
      -- The saved document becomes the new starting point; UI state is kept.
      let state := applyUpdate (model := model) form { state with initial := saved }
        { value := saved, state := state.env, locals := state.locals }
      pure { state with ui := { state.ui with
        pending := false, resultVisible := true, notice := .info "Submitted successfully." } }
    | .rejected feedback => pure (refresh form { state with
        serverFeedback := some feedback
        ui := { (state.ui.announce feedback.message true) with pending := false } })
    | .unreachable message => pure (unreachable message)
  | .loaded request response =>
    match state.cache[request]? with
    | some .loading =>
      let cached := match response with
        | .ok json => .loaded json
        | .error message => .failed message
      pure { state with
        evaluation := ModelView.evaluate form state.value
          (state.cache.insert request cached) state.env state.locals state.evaluation.diagnostics }
    | none
    | some (.loaded _)
    | some (.failed _) => pure state

def execute {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  [Lean.ToJson (Model.Raw model)]
  (form : Model.Component Γ (Model.Raw model) β)
  (state : State form)
  (input : Event (Model.Raw model))
  : Except String (State form) := do
  let state := { state with outbox := [] }
  let state ← event (model := model) form state input
  let state := load form state
  let drafts := state.draftDiagnostics.filter fun draft =>
    state.evaluation.view.controls.any fun control =>
      control.key == draft.control && control.acceptsDrafts
  let state := if drafts == state.draftDiagnostics then state
    else load form (refresh form { state with draftDiagnostics := drafts })
  let outbox := state.outbox.filter (·.applies state.evaluation.view)
  return { state with outbox }

end Forms.Runtime.ModelForm
