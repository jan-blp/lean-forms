module

public import Forms.Runtime.ModelView

@[expose] public section
namespace Forms.Runtime.ModelForm

structure State (raw : Type) where
  initial : raw
  value : raw
  ui : Interaction.State := {}
  validationStarted : Bool := false
  serverFeedback : Option Feedback.ServerError := none
  actions : Nat := 0

def openState {raw : Type} (value : raw) : State raw := { initial := value, value }

inductive Event where
  | draft (key : ControlKey) (value : String)
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

def Command.render : Command → Bool
  | .event (.draft ..) => false
  | _ => true

def validationErrors {model : Type} [FormModel model] [Model.Validation model]
    (value : FormModel.Raw model) : List Feedback.Error :=
  (Model.errors (Model.Validation.validate (model := model) value)).map ModelView.error

structure Snapshot (raw : Type) where
  view : Display.View
  controls : List Display.Control
  value : raw
  ui : Interaction.State
  actions : Nat
  errors : List Feedback.Error
  summary : String
  submissionBlocked : Bool
  render : Bool

def snapshot {model : Type} [FormModel model] [Model.Validation model]
    (form : Model.Component (FormModel.Raw model)) (state : State (FormModel.Raw model))
    (render := true) : Snapshot (FormModel.Raw model) :=
  let errors := validationErrors (model := model) state.value
  let visible := match state.serverFeedback with
    | some feedback => feedback.errors
    | none => if state.validationStarted then errors else []
  let rendered := ModelView.render form state.value visible
  { view := rendered.view, controls := rendered.controls.map (·.view), value := state.value,
    ui := state.ui, actions := state.actions, errors,
    summary := state.serverFeedback.map (·.message) |>.getD (Feedback.summary visible),
    submissionBlocked := !visible.isEmpty, render }

def apply {raw : Type} (form : Model.Component raw) (state : State raw)
    (key : ControlKey) (argument : Option Input) : Except String (State raw) := do
  if state.ui.pending then throw "Submission is in progress."
  let some control := (ModelView.render form state.value).controls.find? (·.key == key)
    | throw "This action is unavailable."
  if control.disabled then throw "This action is unavailable."
  let value ← control.invoke argument
  let controls := (ModelView.render form value).controls
  let drafts := state.ui.drafts.filter fun draft => draft.1 != key && controls.any fun c =>
    c.key == draft.1 && !c.disabled
  pure { state with
    value, actions := state.actions + 1, serverFeedback := none
    ui := { state.ui with drafts, focus := some key, notice := .info "", resultVisible := false } }

def draft {raw : Type} (form : Model.Component raw) (state : State raw)
    (key : ControlKey) (value : String) : Except String (State raw) := do
  if state.ui.pending then return state
  let some control := (ModelView.render form state.value).controls.find? (fun c => c.key == key && !c.disabled)
    | throw "This editor is unavailable."
  let some initial := EditorPresentation.draftValue control.view.input | throw "This control does not accept drafts."
  let drafts := if value == initial then state.ui.drafts.filter (·.1 != key)
    else if state.ui.drafts.any (·.1 == key) then
      state.ui.drafts.map fun entry => if entry.1 == key then (key, value) else entry
    else state.ui.drafts ++ [(key, value)]
  pure { state with ui := { state.ui with drafts } }

def submit {model : Type} [FormModel model] [Model.Validation model]
    (state : State (FormModel.Raw model)) : State (FormModel.Raw model) :=
  if state.ui.pending then state else
  match state.ui.drafts.head? with
  | some (key, _) => { state with ui :=
      { (state.ui.announce "Apply your edits before submitting." true) with focus := some key } }
  | none =>
    let errors := validationErrors (model := model) state.value
    let ui := if errors.isEmpty then
      { state.ui with submission := .requested, notice := .info "Submitting…", focus := none }
      else { (state.ui.announce (Feedback.summary errors) true) with focus := none }
    { state with ui, validationStarted := true, serverFeedback := none }

def event {model : Type} [FormModel model] [Model.Validation model]
    (form : Model.Component (FormModel.Raw model)) (state : State (FormModel.Raw model)) :
    Event → Except String (State (FormModel.Raw model)) := fun event => do
  let state := { state with ui := state.ui.acknowledge }
  match event with
  | .draft key value => draft form state key value
  | .apply key argument =>
    if state.ui.pending then return state
    match apply form state key argument with
    | .ok state => pure state
    | .error message => pure { state with ui := { (state.ui.announce message true) with focus := some key } }
  | .submit => pure (submit (model := model) state)
  | .reset => pure (if state.ui.pending then state else
      { (openState state.initial) with ui := { notice := .info "Started over." } })
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

def execute {model : Type} [FormModel model] [Model.Validation model]
    (form : Model.Component (FormModel.Raw model)) (state : State (FormModel.Raw model)) :
    Command → Except String (State (FormModel.Raw model))
  | .event input => event (model := model) form state input
  | .apply key argument => apply form state key argument
  | .validate => .ok { state with validationStarted := true, serverFeedback := none }
  | .reset => if state.ui.pending then .error "Submission is in progress." else .ok (openState state.initial)
  | .serverError error => .ok { state with serverFeedback := some error }
  | .inspect => .ok state

end Forms.Runtime.ModelForm
