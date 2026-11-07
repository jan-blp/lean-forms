module

public import Forms.Runtime.ComponentHistoryProtocol
public import Forms.Runtime.InputProtocol

@[expose] public section

namespace Forms.Runtime.CompiledView
open Lean Composition

/-- A rendered control retains only its invocation and input schema, not expression JSON. -/
structure Control where
  key : String
  kind : String
  disabled : Bool
  invocation : List (String × Json)
  schema : Option Json := none
  view : Json

structure Rendered where
  view : Json
  controls : List Control := []

def control (target : List Json) (id label kind : String) (disabled : Bool)
    (fields : List (String × Json) := []) (index : Option Nat := none)
    (schema : Option Json := none) : Control :=
  let key := (toJson ([toJson target, toJson id] ++ index.toList.map toJson)).compress
  let invocation := [("target", toJson target), ("action", toJson id)] ++
    index.toList.map fun n => ("index", toJson n)
  { key, kind, disabled, invocation, schema
    view := Json.mkObj ([("key", toJson key), ("id", toJson id), ("target", toJson target),
      ("label", toJson label), ("kind", toJson kind), ("disabled", toJson disabled)] ++ fields) }

def fieldSteps {a b : DataType} (path : Path a b) : List Json :=
  path.toList.map fun name => Json.mkObj [("kind", toJson "field"), ("name", toJson name)]

def itemStep (index : Nat) : Json :=
  Json.mkObj [("kind", toJson "item"), ("index", toJson (toString index))]

def constructorStep (tag : String) : Json :=
  Json.mkObj [("kind", toJson "constructor"), ("tag", toJson tag)]

def editor {ty : DataType} (widget : Widget ty) (value : ⟦ty⟧)
    (target location : List Json) (id label : String) (disabled : Bool) : Control :=
  control target id label "editor" disabled
    [("widget", toJson widget.name), ("schema", ty.toJson),
     ("value", JsonProtocol.valueToJson value), ("location", toJson location)]
    none (some ty.toJson)

def presentation {ty : DataType} (action : WidgetAction ty) (value : ⟦ty⟧)
    (target location : List Json) (id : String) (disabled : Bool) : Control :=
  match action.presentation with
  | .button _ => control target id action.label "button" disabled [("keepDrafts", toJson false)]
  | .editor widget _ => editor widget value target location id action.label disabled

def render {ty : DataType} (component : Component ty) (value : ⟦ty⟧)
    (target : List Json := []) (location : List Json := []) (disabled : Bool := false) : Rendered :=
  match component with
  | .visibleWhen condition body =>
    if condition.eval value then render body value target location disabled else ⟨Json.null, []⟩
  | .disabledWhen condition body => render body value target location (disabled || condition.eval value)
  | .stack (items := items) label children order =>
    let rendered := (FinEnum.toList items).map fun i =>
      render (children (order i)) value (target ++ [toJson (items.label (order i))]) location disabled
    { view := Json.mkObj [("kind", toJson "stack"), ("label", toJson label),
        ("children", toJson ((rendered.filter (·.view != Json.null)).map (·.view)))]
      controls := rendered.flatMap (·.controls) }
  | .field path label widget =>
    let c := editor widget (path.get value) target (location ++ fieldSteps path) "replace" label disabled
    ⟨c.view, [c]⟩
  | .button label _ =>
    let c := control target "press" label "button" disabled [("keepDrafts", toJson false)]
    ⟨c.view, [c]⟩
  | .actionWidget (value := fieldTy) (ids := ids) path label actions =>
    let current := path.get value
    let controls := (FinEnum.toList ids).map fun id =>
      presentation (actions id) current target (location ++ fieldSteps path) (ids.label id) disabled
    { view := Json.mkObj [("kind", toJson "actionWidget"), ("label", toJson label),
        ("schema", fieldTy.toJson), ("value", JsonProtocol.valueToJson current),
        ("location", toJson (location ++ fieldSteps path)), ("children", toJson (controls.map (·.view)))]
      controls }
  | .list path label item _ =>
    let loc := location ++ fieldSteps path
    let add := control target "appendDefault" "Add item" "button" disabled [("keepDrafts", toJson true)]
    let rendered := (path.get value).zipIdx.map fun (v, i) =>
      let body := render item v (target ++ [toJson i]) (loc ++ [itemStep i]) disabled
      let remove := control target "remove" "Remove item" "button" disabled
        [("keepDrafts", toJson false)] (some i)
      (Json.mkObj [("body", body.view), ("remove", remove.view)], body.controls ++ [remove])
    { view := Json.mkObj [("kind", toJson "list"), ("label", toJson label), ("location", toJson loc),
        ("append", add.view), ("items", toJson (rendered.map Prod.fst))]
      controls := add :: rendered.flatMap Prod.snd }
  | .sum (tags := tags) path label branches _ =>
    let current := path.get value
    let tag := tags.label current.tag
    let loc := location ++ fieldSteps path
    let selector := control target "select" label "choice" disabled
      [("location", toJson loc), ("value", toJson tag), ("options", toJson (Enum.options tags))]
    let body := render (branches current.tag) current.payload (target ++ [toJson tag])
      (loc ++ [constructorStep tag]) disabled
    { view := Json.mkObj [("kind", toJson "sum"), ("selector", selector.view), ("body", body.view)]
      controls := selector :: body.controls }
  | .computed (result := result) label expression =>
    ⟨Json.mkObj [("kind", toJson "computed"), ("label", toJson label), ("schema", result.toJson),
      ("value", JsonProtocol.valueToJson (expression.eval value))], []⟩
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
      let some schema := c.schema | throw "Missing editor schema"
      let value ← InputProtocol.evaluate schema raw
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
