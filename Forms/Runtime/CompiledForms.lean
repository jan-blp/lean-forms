module

public import Forms.ExampleForms.Example
public import Forms.Runtime.CompiledView
public import Forms.Runtime.Feedback

@[expose] public section

namespace Forms.Runtime.CompiledForms
open Composition ExampleForms

/-- Client validation deliberately excludes server-only checks. -/
def clientErrors {ty : DataType} (refined : RefinedDataType ty) (value : ⟦ty⟧) :
    List (Validation.CheckedError ty value) :=
  match refined, value with
  | .base _, _ => []
  | .refine inner checked, value => clientErrors inner value ++ checked.checker value
  | .serverRefine inner _, value => clientErrors inner value
  | .list item, values =>
      let items := values.toArray
      (List.finRange values.length).flatMap fun index =>
        (clientErrors item items[index.val]).map fun error =>
          error.mapLocations (fun location => .item index (by simpa [items] using location))
  | .record fields, value => (FinEnum.toList _).flatMap fun name =>
      (clientErrors (fields name) (value name)).map (·.mapLocations (.field name))
  | .sum branches, value =>
      (clientErrors (branches value.tag) value.payload).map (·.mapLocations .constructor)

structure Model (selected : Example) where
  ui : Interaction.State := {}
  validationStarted : Bool := false
  serverFeedback : Option Feedback.ServerError := none
  initial : ⟦selected.definition.ty⟧
  history : ComponentHistory selected.definition.component

def openModel (selected : Example) (initial : ⟦selected.definition.ty⟧) : Model selected :=
  { initial, history := { value := initial } }

structure Action (selected : Example) where
  key : ControlKey
  invocation : Except String selected.definition.component.Invocation

inductive Completion where
  | accepted
  | rejected (feedback : Feedback.ServerError)

inductive Event (selected : Example) where
  | draft (key : ControlKey) (value : String)
  | apply (action : Action selected)
  | submit
  | reset
  | complete (result : Completion)
  | failed (message : String)

inductive Command (selected : Example) where
  | event (event : Event selected)
  | apply (action : Action selected)
  | reset
  | validate
  | serverError (feedback : Feedback.ServerError)
  | inspect

def Command.render {selected : Example} : Command selected → Bool
  | .event (.draft ..) => false
  | _ => true

inductive Effect (selected : Example) where
  | submit (history : ComponentHistory selected.definition.component)

structure Snapshot (selected : Example) where
  view : Display.View
  ui : Interaction.State
  render : Bool
  controls : List Display.Control
  history : ComponentHistory selected.definition.component
  errors : List Feedback.Error
  summary : String
  submissionBlocked : Bool
  effects : List (Effect selected)

def snapshot {selected : Example} (model : Model selected) (render := true) : Snapshot selected :=
  let errors := clientErrors selected.definition.refined model.history.value
  let visible := match model.serverFeedback with
    | some feedback => feedback.errors
    | none => if model.validationStarted then errors.map (fun error => Feedback.ofResolved error.erase) else []
  let rendered := CompiledView.render selected.definition.component model.history.value (errors := visible)
  { view := rendered.view
    ui := model.ui
    render
    controls := rendered.controls.map (·.view)
    history := model.history
    errors := errors.map (fun error => Feedback.ofResolved error.erase)
    summary := match model.serverFeedback with
      | some feedback => feedback.message
      | none => Feedback.summary visible
    submissionBlocked := !visible.isEmpty
    effects := if model.ui.send then [.submit model.history] else [] }

def blockedDraft {selected : Example} (model : Model selected) (key : ControlKey) : Option ControlKey := do
  let c ← (CompiledView.render selected.definition.component model.history.value).controls.find? (·.key == key)
  match c.view.body with
  | .editor .. | .button true => none
  | .choice .. | .button false => model.ui.drafts.head?.map Prod.fst

def apply {selected : Example} (model : Model selected) (action : Action selected) : Except String (Model selected) := do
  if model.ui.pending then throw "Submission is in progress."
  let key := action.key
  if (blockedDraft model key).isSome then throw "Apply your edits before using this control."
  let invocation ← action.invocation
  let history ← (model.history.apply invocation).mapError toString
  let controls := (CompiledView.render selected.definition.component history.value).controls
  let drafts := model.ui.drafts.filter fun draft => draft.1 != key && controls.any fun c =>
    c.key == draft.1 && !c.disabled && match c.view.body with
      | .editor _ input => (EditorPresentation.draftValue input).isSome
      | _ => false
  let ui := { model.ui with drafts, notice := .info "", resultVisible := false, focus := some key }
  pure { model with history, serverFeedback := none, ui }

def draft {selected : Example} (model : Model selected) (key : ControlKey) (value : String) : Except String (Model selected) := do
  if model.ui.pending then return model
  let controls := (CompiledView.render selected.definition.component model.history.value).controls
  let some c := controls.find? (fun c => c.key == key && !c.disabled) | throw "This editor is unavailable."
  let .editor _ input := c.view.body | throw "This control does not accept drafts."
  let some initial := EditorPresentation.draftValue input | throw "This control does not accept drafts."
  let drafts := if value == initial then model.ui.drafts.filter (·.1 != key)
    else if model.ui.drafts.any (·.1 == key) then model.ui.drafts.map fun entry => if entry.1 == key then (key, value) else entry
    else model.ui.drafts ++ [(key, value)]
  pure { model with ui := { model.ui with drafts } }

def startSubmission {selected : Example} (model : Model selected) : Model selected :=
  if model.ui.pending then model else
  match model.ui.drafts.head? with
  | some (key, _) => { model with ui := { (model.ui.announce "Apply your edits before submitting." true) with focus := some key } }
  | none =>
    let errors := (clientErrors selected.definition.refined model.history.value).map (fun error => Feedback.ofResolved error.erase)
    let ui := if errors.isEmpty then
        { model.ui with submission := .requested, notice := .info "Submitting…", focus := none }
      else { (model.ui.announce (Feedback.summary errors) true) with focus := none }
    { model with validationStarted := true, serverFeedback := none, ui }

def event {selected : Example} (model : Model selected) (event : Event selected) : Except String (Model selected) := do
  let model := { model with ui := model.ui.acknowledge }
  match event with
  | .draft key value => draft model key value
  | .apply action =>
    if model.ui.pending then return model
    match apply model action with
    | .ok model => pure model
    | .error error =>
      let focus := (blockedDraft model action.key).getD action.key
      pure { model with ui := { (model.ui.announce error true) with focus := some focus } }
  | .submit => pure (startSubmission model)
  | .reset =>
    if model.ui.pending then return model
    pure { model with history := { value := model.initial }, validationStarted := false, serverFeedback := none, ui := { notice := .info "Started over." } }
  | .complete result =>
    if !model.ui.pending then return model
    match result with
    | .accepted =>
      pure { model with ui := { model.ui with submission := .idle, resultVisible := true, notice := .info "Submitted successfully." } }
    | .rejected feedback =>
      let ui := { (model.ui.announce feedback.message true) with submission := .idle }
      pure { model with serverFeedback := some feedback, ui }
  | .failed message =>
    if !model.ui.pending then return model
    pure { model with ui := { (model.ui.announce message true) with submission := .idle } }

def execute {selected : Example} (model : Model selected) : Command selected → Except String (Model selected)
  | .event input => event model input
  | .apply action => apply model action
  | .reset => do
    if model.ui.pending then throw "Submission is in progress."
    pure { model with history := { value := model.initial }, validationStarted := false, serverFeedback := none, ui := {} }
  | .validate => pure { model with validationStarted := true, serverFeedback := none }
  | .serverError feedback => pure { model with serverFeedback := some feedback }
  | .inspect => pure model

structure Handle where
  value : Nat
  deriving BEq, DecidableEq

/-- IDs are never reused: disposed handles cannot address a later model. -/
structure Store where
  next : Nat := 0
  models : List (Handle × ((selected : Example) × Model selected)) := []
  deriving Inhabited

def Store.find (store : Store) (handle : Handle) : Except String ((selected : Example) × Model selected) :=
  match store.models.find? (·.1 == handle) with
  | some (_, model) => .ok model
  | none => .error "Unknown or disposed form handle"

def Store.insert (store : Store) {selected : Example} (model : Model selected) : Store × Handle :=
  let handle := Handle.mk store.next
  ({ next := store.next + 1, models := (handle, ⟨selected, model⟩) :: store.models }, handle)

def Store.replace (store : Store) (handle : Handle) {selected : Example} (model : Model selected) : Store :=
  { store with models := store.models.map fun (key, current) =>
    (key, if key == handle then ⟨selected, model⟩ else current) }

def Store.dispose (store : Store) (handle : Handle) : Store :=
  { store with models := store.models.filter (·.1 != handle) }

inductive Response where
  | opened {selected : Example} (handle : Handle) (snapshot : Snapshot selected)
  | updated {selected : Example} (snapshot : Snapshot selected)
  | disposed

end Forms.Runtime.CompiledForms
