module

public import Forms.Runtime.ModelView
public import Forms.Runtime.Feedback
public import Forms.Runtime.Interaction
public import Forms.Runtime.FetchState
public import Forms.Model.Requests

@[expose] public section
namespace Forms.Runtime.ModelForm

inductive Effect where
  | submit
  | fetch (fetch : Model.HttpFetch)
  | call (call : Model.HttpCall)
  | focus (key : ControlKey)
  deriving BEq

/-- Whether `view` can still act on `effect`: a focus needs its control to be editable. -/
def Effect.applies (view : Display.View) : Effect → Bool
  | .submit => true
  | .fetch _ => true
  | .call _ => true
  | .focus key => view.controls.any fun control => control.key == key && control.editable

/-- An error about input that cannot enter the model, e.g. "abc" in a natural field; dropped when
the control commits, leaves the view, or its host widget input changes. -/
structure DraftDiagnostic where
  control : ControlKey
  diagnostic : Model.Diagnostic
  deriving BEq

structure State {Γ : Model.Context} {α β : Type} (form : Model.Component Γ α β) where
  /-- Reused until the model, context, fetches, or private state changes. -/
  evaluation : ModelView.Evaluated Γ α form.LocalState β
  initial : α
  initialEnv : Model.Env Γ
  ui : Interaction.State
  serverFeedback : Option Feedback.ServerError
  outbox : List Effect
  validationDiagnostics : List Model.Diagnostic
  reportDiagnostics : List Model.Diagnostic
  supply : Model.Supply
  /-- Counts applied inputs. -/
  epoch : Nat
  draftDiagnostics : List DraftDiagnostic := []
  stateDrafts : List ModelView.ControlMessage

variable {Γ : Model.Context} {α β : Type} {form : Model.Component Γ α β}

abbrev State.value (state : State form) : α := state.evaluation.value
abbrev State.env (state : State form) : Model.Env Γ := state.evaluation.env
abbrev State.fetchState (state : State form) : FetchState := state.evaluation.fetchState
abbrev State.cache (state : State form) : Model.HttpRequest.Cache := state.fetchState.cache
abbrev State.locals (state : State form) : form.LocalState := state.evaluation.locals

def State.calling (state : State form) : Bool :=
  state.evaluation.pending.any (·.waiting.isCall)

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

/-- A restart must pass the old `fetchState`: a new one would accept replies to older fetches. -/
private def openWith
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  (form : Model.Component Γ (Model.Raw model) β)
  (value : Model.Raw model)
  (env : Model.Env Γ)
  (supply : Model.Supply)
  (fetchState : FetchState)
  : State form :=
  let validationDiagnostics := validationErrors (model := model) value
  let reportDiagnostics := reports (model := model) value true
  { evaluation := ModelView.evaluate form value fetchState env form.initialState
      (validationDiagnostics ++ reportDiagnostics) []
    initial := value
    initialEnv := env
    ui := .initial
    serverFeedback := none
    outbox := []
    validationDiagnostics
    reportDiagnostics
    supply
    epoch := 0
    stateDrafts := [] }

@[no_expose] def openState
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  (form : Model.Component Γ (Model.Raw model) β)
  (value : Model.Raw model)
  (env : Model.Env Γ)
  (supply : Model.Supply)
  : State form :=
  openWith (model := model) form value env supply .empty

def refresh
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  : State form :=
  let diagnostics := state.draftDiagnostics.map (·.diagnostic) ++
    (state.serverFeedback.map (·.errors)).getD state.validationDiagnostics ++
    state.reportDiagnostics
  if diagnostics == state.evaluation.diagnostics &&
      state.stateDrafts == state.evaluation.controlMessages then state else
    { state with
      evaluation := ModelView.evaluate form state.value state.fetchState state.env state.locals
        diagnostics state.stateDrafts }

/-- Marks the requests `form` reads but has not loaded as loading, and queues them. -/
def load
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  : State form :=
  let queued := state.fetchState.queue state.evaluation.requests
  if queued.fetches.isEmpty then state else
    let evaluation := ModelView.evaluate form state.value queued.state state.env state.locals
      state.evaluation.diagnostics state.evaluation.controlMessages
    let outbox := state.outbox.filter (·.applies evaluation.view)
    { state with
      evaluation
      outbox := outbox ++ queued.fetches.map .fetch }

/-- Starts over from `initial`, keeping pending and loaded responses; failed ones are retried. -/
@[no_expose] def restart
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  {form : Model.Component Γ (Model.Raw model) β}
  (state : State form)
  : State form :=
  openWith (model := model) form state.initial state.initialEnv state.supply
    state.fetchState.retryFailed

theorem restart_fetchState
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  {form : Model.Component Γ (Model.Raw model) β}
  (state : State form)
  : (restart (model := model) state).fetchState = state.fetchState.retryFailed := by
  unfold restart openWith
  rfl

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
  | loaded (fetch : Model.HttpFetch) (response : Except String Lean.Json)
  | called (id : Model.Uuid) (result : Except String Lean.Json)

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
  | idCollision (id : Model.Uuid)
  deriving DecidableEq, Repr

instance : ToString Rejection where
  toString
    | .input message => message
    | .stale error => toString error
    | .clientBug error => toString error
    | .idCollision id => s!"The new item drew the id {id.value}, which is already used. \
      This is a bug; please contact BLP."

def Rejection.ofDecode : DecodeError → Rejection
  | .input message => .input message
  | .clientBug error => .clientBug error

def Rejection.ofAction : ModelView.ActionError → Rejection
  | .decode error => .ofDecode error
  | .invalid error => .stale (.invocation error)
  | .idCollision id => .idCollision id

def validateAction
  {Γ : Model.Context}
  {α β : Type}
  (form : Model.Component Γ α β)
  (state : State form)
  (key : ControlKey)
  (argument : Option Input)
  (epoch : Nat)
  : StateT Model.Supply (Except Rejection) (Model.ComponentUpdate Γ α form.LocalState) :=
  fun supply => do
    if state.ui.pending then throw (.stale .pending)
    state.evaluation.applyKey key argument epoch |>.run supply |>.mapError .ofAction

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
  let fetchState := state.fetchState.invalidate updated.invalidations
  let fetchState := match updated.call with
    | some call => fetchState.send call
    | none => fetchState
  let evaluation :=
    ModelView.evaluate form updated.value fetchState updated.state updated.locals diagnostics
      state.stateDrafts
  let focus := updated.visit.bind (evaluation.view.resolve ·.locations)
  { state with
    evaluation
    validationDiagnostics
    reportDiagnostics
    serverFeedback := none
    outbox := state.outbox ++ focus.toList.map .focus ++ updated.call.toList.map .call
    ui := { state.ui with notice := .info "", resultVisible := false } }

/-- Runs the reactions `epoch` made pending, innermost first, each on a fresh evaluation.
A reaction never makes another one pending, so `fuel` starts at the number pending after the input. -/
def react
  {Γ : Model.Context}
  {model β : Type}
  [FormModel model]
  [Model.Validation model]
  [Model.Reports model]
  [Lean.ToJson (Model.Raw model)]
  (form : Model.Component Γ (Model.Raw model) β)
  (state : State form)
  (epoch : Nat)
  : (fuel : Nat) → Except Rejection (State form)
  | 0 => pure state
  | fuel + 1 => match state.evaluation.pending.filter (·.waiting == .reaction epoch) with
    | [] => pure state
    | pending :: _ => do
      let (updated, supply) ←
        ((state.evaluation.apply pending.route .react).run state.supply).mapError .ofAction
      react form (applyUpdate (model := model) form { state with supply } updated) epoch fuel

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
  let epoch := state.epoch + 1
  let (updated, supply) ← (validateAction form state key argument epoch).run state.supply
  let state := { state with
    supply
    epoch
    draftDiagnostics := state.draftDiagnostics.filter (·.control != key)
    stateDrafts := state.stateDrafts.filter (·.control != key) }
  let state := applyUpdate (model := model) form state updated
  let state ← react (model := model) form state epoch
    (state.evaluation.pending.filter (·.waiting == .reaction epoch)).length
  let drafts := state.draftDiagnostics.filter fun draft =>
    state.evaluation.view.controls.any (·.key == draft.control)
  return refresh form { state with draftDiagnostics := drafts }

def keepRejected
  {Γ : Model.Context}
  {α β : Type}
  {form : Model.Component Γ α β}
  (state : State form)
  (key : ControlKey)
  (message : String)
  : State form :=
  match key with
  | .edit location
  | .select location =>
    { state with
      draftDiagnostics :=
        { control := key
          diagnostic := { kind := .error, message, targets := .locations location [] } } ::
          state.draftDiagnostics.filter (·.control != key) }
  | .state .. =>
    { state with
      stateDrafts := { control := key, message := { kind := .error, text := message } } ::
        state.stateDrafts.filter (·.control != key) }
  | .press ..
  | .tab .. => state

def disabledChoices (view : Display.View) : List Model.Diagnostic :=
  view.controls.filterMap fun control => control.input.disabledChoice.map fun message =>
    { kind := .error, message, targets := .locations control.location [] }

def submit
  {Γ : Model.Context}
  {α β : Type}
  {form : Model.Component Γ α β}
  (state : State form)
  : State form :=
  if state.ui.pending then state else
  if state.calling then
    { state with ui := state.ui.announce "Wait for the pending request, then submit again." true }
  else
  let errors := state.validationDiagnostics
  let state := refresh form { state with serverFeedback := none }
  let disabled := disabledChoices state.evaluation.view
  if errors.isEmpty && state.draftDiagnostics.isEmpty && disabled.isEmpty then
    { state with
      ui := { state.ui with pending := true, notice := .info "Submitting…" }
      outbox := state.outbox ++ [.submit] }
  else
    let diagnostics := state.draftDiagnostics.map (·.diagnostic) ++ disabled ++ errors
    let focus := state.evaluation.view.resolveFirst (diagnostics.map (·.locations))
    { state with
      ui := state.ui.announce (Model.Diagnostic.summary diagnostics) true
      outbox := state.outbox ++ focus.toList.map .focus }

theorem submit_calling
  {Γ : Model.Context}
  {α β : Type}
  {form : Model.Component Γ α β}
  (state : State form)
  (calling : state.calling)
  : (submit state).outbox = state.outbox ∧ (submit state).ui.pending = state.ui.pending := by
  unfold submit
  split <;> simp_all [Interaction.State.announce]

theorem submit_disabledChoice
  {Γ : Model.Context}
  {α β : Type}
  {form : Model.Component Γ α β}
  (state : State form)
  (fresh : Effect.submit ∉ state.outbox)
  (submitted : Effect.submit ∈ (submit state).outbox)
  : ∀ control ∈ (submit state).evaluation.view.controls, control.input.disabledChoice = none := by
  have keeps : (refresh form { state with serverFeedback := none }).outbox = state.outbox := by
    unfold refresh
    simp only
    split <;> rfl
  intro control shown
  unfold submit at submitted shown
  by_cases pending : state.ui.pending = true
  · simp only [ite_eq_left pending] at submitted
    contradiction
  by_cases calling : state.calling = true
  · simp only [ite_eq_right pending, ite_eq_left calling] at submitted
    contradiction
  simp only [ite_eq_right pending, ite_eq_right calling] at submitted shown
  generalize refresh form { state with serverFeedback := none } = refreshed at keeps submitted shown
  by_cases clean : (state.validationDiagnostics.isEmpty && refreshed.draftDiagnostics.isEmpty &&
      (disabledChoices refreshed.evaluation.view).isEmpty) = true
  · simp only [ite_eq_left clean] at shown
    simp only [Bool.and_eq_true, List.isEmpty_iff] at clean
    simp only [disabledChoices, List.filterMap_eq_nil_iff, Option.map_eq_none_iff] at clean
    exact clean.2 control shown
  · rw [ite_eq_right clean] at submitted
    simp [keeps, fresh] at submitted

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
      let state ← match rejection with
        | .clientBug error => throw (toString error)
        | .idCollision _ => throw message
        | .input _ =>
          let typed := argument.any Input.keepsRejection &&
            state.evaluation.view.controls.any (·.key == key)
          pure (if typed then keepRejected state key message else state)
        | .stale _ => pure state
      pure (refresh form { state with ui := { ui with rejection := some message } })
  | .draft key message =>
    if state.ui.pending then return state
    let some control := state.evaluation.view.controls.find? (·.key == key) | return state
    unless control.acceptsDrafts do
      return refresh form { state with stateDrafts := state.stateDrafts.filter (·.control != key) }
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
      -- The saved document becomes the new starting point; UI state is kept.
      let state := applyUpdate (model := model) form { state with initial := saved }
        { value := saved, state := state.env, locals := state.locals
          invalidations := [], call := none }
      pure { state with ui := { state.ui with
        pending := false, resultVisible := true, notice := .info "Submitted successfully." } }
    | .rejected feedback => pure (refresh form { state with
        serverFeedback := some feedback
        ui := { (state.ui.announce feedback.message true) with pending := false } })
    | .unreachable message => pure (unreachable message)
  | .loaded fetch response =>
    match state.fetchState.accept fetch response with
    | none => pure state
    | some fetchState =>
      pure { state with
        evaluation := ModelView.evaluate form state.value fetchState state.env state.locals
          state.evaluation.diagnostics state.evaluation.controlMessages }
  | .called id result =>
    let some fetchState := state.fetchState.finish id | pure state
    let finished := { state with
      evaluation := ModelView.evaluate form state.value fetchState state.env state.locals
        state.evaluation.diagnostics state.evaluation.controlMessages }
    if state.ui.pending then return finished
    let some pending := state.evaluation.pending.find? (·.waiting == .call id) | pure finished
    match (state.evaluation.apply pending.route (.resume id result)).run state.supply with
    | .ok (updated, supply) =>
      pure (applyUpdate (model := model) form { finished with supply } updated)
    | .error (.idCollision collision) => throw (toString (Rejection.idCollision collision))
    | .error (.decode _)
    | .error (.invalid _) => pure finished

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
  let before := state.evaluation.view.controls
  let state := { state with outbox := [] }
  let state ← event (model := model) form state input
  let state := load form state
  let holds (control : Display.Control) := before.all fun old =>
    old.key != control.key || !old.input.retiresRejection control.input
  let drafts := state.draftDiagnostics.filter fun draft =>
    state.evaluation.view.controls.any fun control =>
      control.key == draft.control && control.acceptsDrafts && holds control
  let stateDrafts := state.stateDrafts.filter fun draft =>
    state.evaluation.view.controls.any fun control =>
      control.key == draft.control && !control.disabled && holds control
  let state := if drafts == state.draftDiagnostics && stateDrafts == state.stateDrafts then state
    else load form (refresh form { state with draftDiagnostics := drafts, stateDrafts })
  let outbox := state.outbox.filter (·.applies state.evaluation.view)
  return { state with outbox }

end Forms.Runtime.ModelForm
