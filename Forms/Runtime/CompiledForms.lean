module

public import Forms.ExampleForms.Example
public import Forms.Runtime.CompiledView
public import Forms.Runtime.ComponentHistoryProtocol
public import Forms.Runtime.Feedback

@[expose] public section

namespace Forms.Runtime.CompiledForms
open Lean Composition ExampleForms

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

/-- `revision` is `compiledRevision`, passed in so that it can hash this module. -/
def descriptor (revision : String) (selected : Example) : Json :=
  let definition := selected.definition
  Json.mkObj [("form", toJson selected.name), ("revision", toJson revision),
    ("value", JsonProtocol.valueToJson definition.initial)]

structure Model (selected : Example) where
  ui : Interaction.State := {}
  validationStarted : Bool := false
  serverFeedback : Option Feedback.ServerError := none
  initial : ⟦selected.definition.ty⟧
  history : ComponentHistory selected.definition.component

def openModel (request : Json) : Except String ((selected : Example) × Model selected) := do
  let name ← request.getObjValAs? String "form"
  let some selected := Example.ofName name | throw s!"Unknown compiled form: {name}"
  let definition := selected.definition
  let initial ← JsonProtocol.valueFromJson definition.ty (← request.getObjVal? "value")
  pure ⟨selected, { initial, history := { value := initial } }⟩

def snapshot {selected : Example} (model : Model selected) : Json :=
  let errors := clientErrors selected.definition.refined model.history.value
  let visible := match model.serverFeedback with
    | some feedback => feedback.errors
    | none => if model.validationStarted then errors.map (fun error => Feedback.ofResolved error.erase) else []
  let rendered := CompiledView.render selected.definition.component model.history.value (errors := visible)
  let title := rendered.view.title
  let summary := match model.serverFeedback with
    | some feedback => feedback.message
    | none => Feedback.summary visible
  Json.mkObj [("summary", toJson summary), ("submissionBlocked", toJson (!visible.isEmpty)),
    ("view", DisplayProtocol.viewToJson rendered.view model.ui),
    ("ui", Json.mkObj [("status", toJson model.ui.status), ("error", toJson model.ui.error),
      ("pending", toJson model.ui.pending), ("send", toJson model.ui.send), ("focus", toJson model.ui.focus),
      ("count", toJson (s!"{model.history.actions.size} " ++ if model.history.actions.size == 1 then "action" else "actions")),
      ("result", if model.ui.resultVisible then toJson (JsonProtocol.valueToJson model.history.value).pretty else Json.null)]),
    ("controls", toJson (rendered.controls.map (fun c => DisplayProtocol.controlToJson c.view))),
    ("title", toJson title), ("submission", ComponentHistoryProtocol.encode model.history),
    ("errors", toJson (errors.map (fun error => error.erase.toJson)))]

def blockedDraft {selected : Example} (model : Model selected) (key : String) : Option String := do
  let c ← (CompiledView.render selected.definition.component model.history.value).controls.find? (·.key == key)
  match c.view.body with
  | .editor .. | .button true => none
  | .choice .. | .button false => model.ui.drafts.head?.map Prod.fst

def apply {selected : Example} (model : Model selected) (request : Json) : Except String (Model selected) := do
  if model.ui.pending then throw "Submission is in progress."
  let key ← request.getObjValAs? String "key"
  if (blockedDraft model key).isSome then throw "Apply your edits before using this control."
  let invocation ← CompiledView.invocation selected.definition.component model.history.value key
    (request.getObjVal? "argument").toOption
  let history ← (model.history.apply invocation).mapError toString
  let controls := (CompiledView.render selected.definition.component history.value).controls
  let drafts := model.ui.drafts.filter fun draft => draft.1 != key && controls.any fun c =>
    c.key == draft.1 && !c.disabled && match c.view.body with
      | .editor _ input => (EditorPresentation.draftValue input).isSome
      | _ => false
  let ui := { model.ui with drafts, notice := .info "", resultVisible := false, focus := some key }
  pure { model with history, serverFeedback := none, ui }

def draft {selected : Example} (model : Model selected) (key value : String) : Except String (Model selected) := do
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

def event {selected : Example} (model : Model selected) (request : Json) : Except String (Model selected) := do
  let name ← request.getObjValAs? String "event"
  let model := { model with ui := model.ui.acknowledge }
  match name with
  | "draft" => draft model (← request.getObjValAs? String "key") (← request.getObjValAs? String "argument")
  | "apply" =>
    if model.ui.pending then return model
    match apply model request with
    | .ok model => pure model
    | .error error =>
      let key := (request.getObjValAs? String "key").toOption
      let focus := (key.bind (blockedDraft model)).or key
      pure { model with ui := { (model.ui.announce error true) with focus } }
  | "submit" => pure (startSubmission model)
  | "reset" =>
    if model.ui.pending then return model
    pure { model with history := { value := model.initial }, validationStarted := false, serverFeedback := none, ui := { notice := .info "Started over." } }
  | "complete" =>
    if !model.ui.pending then return model
    let status ← request.getObjValAs? Nat "status"
    if 200 ≤ status && status < 300 then
      pure { model with ui := { model.ui with submission := .idle, resultVisible := true, notice := .info "Submitted successfully." } }
    else
      let feedback := FeedbackProtocol.serverError status (← request.getObjValAs? String "body")
      let ui := { (model.ui.announce feedback.message true) with submission := .idle }
      pure { model with serverFeedback := some feedback, ui }
  | "failed" =>
    if !model.ui.pending then return model
    pure { model with ui := { (model.ui.announce (← request.getObjValAs? String "message") true) with submission := .idle } }
  | _ => throw s!"Unknown UI event: {name}"

/-- IDs are never reused: disposed handles cannot address a later model. -/
structure Store where
  next : Nat := 0
  models : List (Nat × ((selected : Example) × Model selected)) := []
  deriving Inhabited

def execute (revision : String) (store : Store) (request : Json) : Except String (Store × Json) := do
  let operation ← request.getObjValAs? String "operation"
  if operation == "open" then
    let expected ← request.getObjValAs? String "revision"
    unless expected == revision do
      throw "Compiled form version differs from the server. Rebuild Wasm and reload."
    let model ← openModel request
    pure ({ next := store.next + 1, models := (store.next, model) :: store.models },
      Json.mkObj [("handle", toJson (toString store.next)), ("snapshot", snapshot model.2)])
  else
    let idText ← request.getObjValAs? String "handle"
    let some id := idText.toNat? | throw "Invalid form handle"
    let some (_, ⟨selected, model⟩) := store.models.find? (·.1 == id) | throw "Unknown or disposed form handle"
    if operation == "dispose" then
      pure ({ store with models := store.models.filter (·.1 != id) }, Json.null)
    else
      let model ← match operation with
        | "event" => event model request
        | "apply" => apply model request
        | "reset" => do
          if model.ui.pending then throw "Submission is in progress."
          pure { model with history := { value := model.initial }, validationStarted := false, serverFeedback := none, ui := {} }
        | "validate" => pure { model with validationStarted := true, serverFeedback := none }
        | "serverError" => do
          let status ← request.getObjValAs? Nat "status"
          let body ← request.getObjValAs? String "body"
          pure { model with serverFeedback := some (FeedbackProtocol.serverError status body) }
        | "inspect" => pure model
        | _ => throw s!"Unknown form operation: {operation}"
      let response := snapshot model
      pure ({ store with models := store.models.map fun (key, current) =>
        (key, if key == id then ⟨selected, model⟩ else current) }, response)

/-- Wasm transport: JSON text in, `{ok, value}` or `{ok, error}` out. Failures keep the store. -/
def respond (revision : String) (store : Store) (text : String) : Store × String :=
  match Json.parse text >>= execute revision store with
  | .error error => (store, (Json.mkObj [("ok", toJson false), ("error", toJson error)]).compress)
  | .ok (store, value) => (store, (Json.mkObj [("ok", toJson true), ("value", value)]).compress)

end Forms.Runtime.CompiledForms
