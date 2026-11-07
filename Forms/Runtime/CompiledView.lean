module

public import Forms.Runtime.ComponentHistoryProtocol
public import Forms.Runtime.InputProtocol
public import Forms.Runtime.FeedbackProtocol

@[expose] public section

namespace Forms.Runtime.CompiledView
open Lean Composition

/-- A rendered control retains its invocation and typed input normalizer. -/
structure Control where
  key : String
  kind : String
  disabled : Bool
  invocation : List (String × Json)
  normalize : Option (Json → Except String Json) := none
  view : Json

structure Rendered where
  view : Json
  controls : List Control := []

def control (target : List Json) (id label kind : String) (disabled : Bool)
    (fields : List (String × Json) := []) (index : Option Nat := none)
    (normalize : Option (Json → Except String Json) := none) : Control :=
  let key := (toJson ([toJson target, toJson id] ++ index.toList.map toJson)).compress
  let invocation := [("target", toJson target), ("action", toJson id)] ++
    index.toList.map fun n => ("index", toJson n)
  { key, kind, disabled, invocation, normalize
    view := Json.mkObj ([("key", toJson key), ("id", toJson id), ("target", toJson target),
      ("label", toJson label), ("kind", toJson kind), ("disabled", toJson disabled)] ++ fields) }

def fieldSteps {a b : DataType} (path : Path a b) : Feedback.Location :=
  path.toList.map Feedback.Step.field

/-- Serialize already resolved feedback alongside the display node. -/
def feedbackFields (errors : List Feedback.Error) (location : Feedback.Location) : List (String × Json) :=
  (Feedback.messages errors location).toList.map fun message => ("messages", toJson message)

/-- Display text is formatted from the Lean type, never from a schema in the browser. -/
def formatValue {ty : DataType} (value : ⟦ty⟧) : String :=
  match ty with
  | .text => value
  | .natural => toString value
  | .boolean => if value then "true" else "false"
  | .date => Date.toString value
  | .enum domain => domain.label value
  | .list _ => "[" ++ String.intercalate ", " (value.map formatValue) ++ "]"
  | .record names _ => "{" ++ String.intercalate ", " ((FinEnum.toList names).map fun name =>
      names.label name ++ ": " ++ formatValue (value name)) ++ "}"
  | .sum tags _ => tags.label value.tag ++ ": " ++ formatValue value.payload

def editor {ty : DataType} (widget : Widget ty) (value : ⟦ty⟧)
    (target : List Json) (location : Feedback.Location) (id label : String) (disabled : Bool) (errors : List Feedback.Error := []) : Control :=
  control target id label "editor" disabled
    ([("widget", toJson widget.name),
      ("value", JsonProtocol.valueToJson value), ("location", FeedbackProtocol.locationToJson location)] ++ feedbackFields errors location ++
      match widget with
      | .select (domain := domain) => [("options", toJson (Enum.options domain))]
      | _ => [])
    none (some (InputProtocol.normalize ty))

def presentation {ty : DataType} (action : WidgetAction ty) (value : ⟦ty⟧)
    (target : List Json) (location : Feedback.Location) (id : String) (disabled : Bool) (errors : List Feedback.Error := []) : Control :=
  match action.presentation with
  | .button _ => control target id action.label "button" disabled [("keepDrafts", toJson false)]
  | .editor widget _ => editor widget value target location id action.label disabled errors

def render {ty : DataType} (component : Component ty) (value : ⟦ty⟧)
    (target : List Json := []) (location : Feedback.Location := []) (disabled : Bool := false)
    (errors : List Feedback.Error := []) : Rendered :=
  match component with
  | .visibleWhen condition body =>
    if condition.eval value then render body value target location disabled errors else ⟨Json.null, []⟩
  | .disabledWhen condition body => render body value target location (disabled || condition.eval value) errors
  | .stack (items := items) label children order =>
    let rendered := (FinEnum.toList items).map fun i =>
      render (children (order i)) value (target ++ [toJson (items.label (order i))]) location disabled errors
    { view := Json.mkObj [("kind", toJson "stack"), ("label", toJson label),
        ("children", toJson ((rendered.filter (·.view != Json.null)).map (·.view)))]
      controls := rendered.flatMap (·.controls) }
  | .field path label widget =>
    let c := editor widget (path.get value) target (location ++ fieldSteps path) "replace" label disabled errors
    ⟨c.view, [c]⟩
  | .button label _ =>
    let c := control target "press" label "button" disabled [("keepDrafts", toJson false)]
    ⟨c.view, [c]⟩
  | .actionWidget (ids := ids) path label actions =>
    let current := path.get value
    let controls := (FinEnum.toList ids).map fun id =>
      presentation (actions id) current target (location ++ fieldSteps path) (ids.label id) disabled errors
    let ownsFeedback := !(FinEnum.toList ids).any fun id => match (actions id).presentation with
      | .editor _ _ => true
      | .button _ => false
    { view := Json.mkObj ([("kind", toJson "actionWidget"), ("label", toJson label),
        ("text", toJson (formatValue current)),
        ("location", FeedbackProtocol.locationToJson (location ++ fieldSteps path)), ("children", toJson (controls.map (·.view)))] ++
        if ownsFeedback then feedbackFields errors (location ++ fieldSteps path) else [])
      controls }
  | .list path label item _ =>
    let loc := location ++ fieldSteps path
    let add := control target "appendDefault" "Add item" "button" disabled [("keepDrafts", toJson true)]
    let rendered := (path.get value).zipIdx.map fun (v, i) =>
      let body := render item v (target ++ [toJson i]) (loc ++ [.item i]) disabled errors
      let remove := control target "remove" "Remove item" "button" disabled
        [("keepDrafts", toJson false)] (some i)
      (Json.mkObj [("body", body.view), ("remove", remove.view)], body.controls ++ [remove])
    { view := Json.mkObj ([("kind", toJson "list"), ("label", toJson label), ("location", FeedbackProtocol.locationToJson loc),
        ("append", add.view), ("items", toJson (rendered.map Prod.fst))] ++ feedbackFields errors loc)
      controls := add :: rendered.flatMap Prod.snd }
  | .sum (tags := tags) path label branches _ =>
    let current := path.get value
    let tag := tags.label current.tag
    let loc := location ++ fieldSteps path
    let selector := control target "select" label "choice" disabled
      ([("location", FeedbackProtocol.locationToJson loc), ("value", toJson tag), ("options", toJson (Enum.options tags))] ++ feedbackFields errors loc)
    let body := render (branches current.tag) current.payload (target ++ [toJson tag])
      (loc ++ [.constructor tag]) disabled errors
    { view := Json.mkObj [("kind", toJson "sum"), ("selector", selector.view), ("body", body.view)]
      controls := selector :: body.controls }
  | .computed label expression =>
    ⟨Json.mkObj [("kind", toJson "computed"), ("label", toJson label),
      ("text", toJson (formatValue (expression.eval value)))], []⟩
  | .text expression => ⟨Json.mkObj [("kind", toJson "text"), ("value", toJson (expression.eval value))], []⟩
  | .table rows columns =>
    ⟨Json.mkObj [("kind", toJson "table"), ("columns", toJson (columns.map (·.label))),
      ("rows", toJson ((rows.eval value).map fun row => columns.map fun column => column.format.eval row))], []⟩

/-- The browser sends only a control key and raw argument. Resolve both against the current view. -/
def invocation {ty : DataType} (component : Component ty) (value : ⟦ty⟧)
    (key : String) (argument : Option Json) : Except String component.Invocation := do
  let some c := (render component value).controls.find? (·.key == key)
    | throw "This action is unavailable."
  if c.disabled then throw "This action is unavailable."
  let fields ← match c.kind, argument with
    | "editor", some raw => do
      let some normalize := c.normalize | throw "Missing editor normalizer"
      let value ← normalize raw
      pure [("argument", value)]
    | "choice", some raw => do
      let tag ← raw.getStr?
      pure [("constructor", toJson tag)]
    | "button", none => pure []
    | "button", some _ => throw "Buttons do not accept an argument."
    | _, _ => throw "Missing action argument."
  let json := Json.mkObj (c.invocation ++ fields)
  let target ← (← json.getObjVal? "target").getArr?
  (ComponentHistoryProtocol.invocationFromJson component target.toList json).mapError toString

end Forms.Runtime.CompiledView
