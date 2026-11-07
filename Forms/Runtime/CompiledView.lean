module

public import Forms.Core.ComponentHistory
public import Forms.Runtime.Input
public import Forms.Runtime.DisplayProtocol

@[expose] public section

namespace Forms.Runtime.CompiledView
open Composition

/-- Each control decodes its boundary argument directly into a typed invocation. -/
structure Control (invocation : Type) where
  invoke : Option Input → Except String invocation
  view : Display.Control

def Control.key {α : Type} (control : Control α) : ControlKey := control.view.key
def Control.kind {α : Type} (control : Control α) : Display.ControlKind := control.view.kind
def Control.disabled {α : Type} (control : Control α) : Bool := control.view.disabled

def Control.map {α β : Type} (f : α → β) (control : Control α) : Control β :=
  { control with invoke := fun argument => (control.invoke argument).map f }

structure Rendered (invocation : Type) where
  view : Display.View
  controls : List (Control invocation) := []

def Rendered.map {α β : Type} (f : α → β) (rendered : Rendered α) : Rendered β :=
  { rendered with controls := rendered.controls.map (Control.map f) }

def control {α : Type} (target : Display.Target) (id label : String) (body : Display.ControlBody)
    (disabled : Bool) (invoke : Option Input → Except String α)
    (messages : Option String := none) (index : Option Nat := none) : Control α :=
  { invoke
    view := { key := DisplayProtocol.controlKey target id index, id, target, label, disabled, body, messages } }

def noArgument {α : Type} (invocation : α) : Option Input → Except String α
  | none => .ok invocation
  | some _ => .error "Buttons do not accept an argument."

def requiredArgument {α : Type} (decode : Input → Except String α) : Option Input → Except String α
  | some raw => decode raw
  | none => .error "Missing action argument."

def fieldSteps {a b : DataType} (path : Path a b) : Feedback.Location :=
  match path with
  | .self => []
  | .field (fieldNames := names) name rest => .field (names.label name) :: fieldSteps rest

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
    (target : Display.Target) (location : Feedback.Location) (id label : String) (disabled : Bool)
    (errors : List Feedback.Error := []) : Control ⟦ty⟧ :=
  let input : Display.Editor := match widget with
    | .textInput => .text value
    | .naturalInput => .natural value
    | .dateInput => .date value
    | .checkbox => .checkbox value
    | .select (domain := domain) => .select (Display.Selection.ofEnum domain value)
  control target id label (.editor location input) disabled (requiredArgument (Input.decode ty))
    (Feedback.messages errors location)

def presentation {ty : DataType} (action : WidgetAction ty) (value : ⟦ty⟧)
    (target : Display.Target) (location : Feedback.Location) (id : String) (disabled : Bool) (errors : List Feedback.Error := []) : Control action.presentation.Argument :=
  match action.presentation with
  | .button _ => control target id action.label (.button false) disabled (noArgument ())
  | .editor widget _ => editor widget value target location id action.label disabled errors

def render {ty : DataType} (component : Component ty) (value : ⟦ty⟧)
    (target : Display.Target := []) (location : Feedback.Location := []) (disabled : Bool := false)
    (errors : List Feedback.Error := []) : Rendered component.Invocation :=
  match component with
  | .visibleWhen condition body =>
    if condition value then render body value target location disabled errors else ⟨.hidden, []⟩
  | .disabledWhen condition body => render body value target location (disabled || condition value) errors
  | .stack (items := items) label children order =>
    let rendered := (FinEnum.toList items).map fun i =>
      (render (children (order i)) value (target ++ [.name (items.label (order i))]) location disabled errors).map
        (fun invocation => ⟨order i, invocation⟩)
    { view := .stack label ((rendered.filter (! ·.view.isHidden)).map (·.view))
      controls := rendered.flatMap (·.controls) }
  | .field path label widget =>
    let c := (editor widget (path.get value) target (location ++ fieldSteps path) "replace" label disabled errors).map
      (fun argument => ⟨Action.Field.replace, argument⟩)
    ⟨.control c.view, [c]⟩
  | .button label _ =>
    let c := control target "press" label (.button false) disabled (noArgument Action.Button.press)
    ⟨.control c.view, [c]⟩
  | .actionWidget (ids := ids) path label actions =>
    let current := path.get value
    let controls := (FinEnum.toList ids).map fun id =>
      (presentation (actions id) current target (location ++ fieldSteps path) (ids.label id) disabled errors).map
        (fun argument => ⟨id, argument⟩)
    let ownsFeedback := !(FinEnum.toList ids).any fun id => match (actions id).presentation with
      | .editor _ _ => true
      | .button _ => false
    { view := .actionWidget label (formatValue current) (location ++ fieldSteps path) (controls.map (·.view))
        (if ownsFeedback then Feedback.messages errors (location ++ fieldSteps path) else none)
      controls }
  | .list path label item _ =>
    let loc := location ++ fieldSteps path
    let add := control target "appendDefault" "Add item" (.button true) disabled
      (noArgument (Action.List.appendDefault (itemInvocation := item.Invocation)))
    let rendered := (path.get value).zipIdx.map fun (v, i) =>
      let body := (render item v (target ++ [.index i]) (loc ++ [.item i]) disabled errors).map (Action.List.item i)
      let remove := control target "remove" "Remove item" (.button false) disabled (noArgument (Action.List.remove i))
        none (some i)
      ((body.view, remove.view), body.controls ++ [remove])
    { view := .list label loc (rendered.map Prod.fst) add.view (Feedback.messages errors loc)
      controls := add :: rendered.flatMap Prod.snd }
  | .sum (tags := tags) path label branches _ =>
    let current := path.get value
    let tag := tags.label current.tag
    let loc := location ++ fieldSteps path
    let selector := control target "select" label (.choice loc tag (Enum.options tags)) disabled (requiredArgument fun raw => do
      let .text name := raw | throw "Expected a constructor name."
      let some selected := (FinEnum.toList tags).find? (fun t => tags.label t == name)
        | throw s!"Unknown constructor: {name}"
      pure (Action.Sum.select selected))
      (Feedback.messages errors loc)
    let body := (render (branches current.tag) current.payload (target ++ [.name tag])
      (loc ++ [.constructor tag]) disabled errors).map (Action.Sum.inPayload current.tag)
    { view := .sum selector.view body.view
      controls := selector :: body.controls }
  | .computed label expression => ⟨.computed label (formatValue (expression value)), []⟩
  | .text expression => ⟨.text (expression value), []⟩
  | .table rows columns =>
    ⟨.table (columns.map (·.label))
      ((rows value).map fun row => columns.map fun column => column.format row), []⟩

/-- The browser sends only a control key and raw argument. Resolve both against the current view. -/
def invocation {ty : DataType} (component : Component ty) (value : ⟦ty⟧)
    (key : ControlKey) (argument : Option Input) : Except String component.Invocation := do
  let some c := (render component value).controls.find? (·.key == key)
    | throw "This action is unavailable."
  if c.disabled then throw "This action is unavailable."
  c.invoke argument

end Forms.Runtime.CompiledView
