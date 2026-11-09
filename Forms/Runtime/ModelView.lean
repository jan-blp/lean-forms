module

public import Forms.Model.Component
public import Forms.Runtime.Input
public import Forms.Runtime.DisplayProtocol

@[expose] public section
namespace Forms.Runtime.ModelView
open Forms.Model

/-- Each control decodes its boundary argument directly into a typed invocation. -/
structure Control (invocation : Type) where
  invoke : Option Input → Except String invocation
  view : Display.Control

def Control.key {α : Type} (control : Control α) : ControlKey := control.view.key
def Control.disabled {α : Type} (control : Control α) : Bool := control.view.disabled

def Control.map {α β : Type} (f : α → β) (control : Control α) : Control β :=
  { control with invoke := fun argument => (control.invoke argument).map f }

structure Rendered (invocation : Type) where
  view : Display.View
  controls : List (Control invocation) := []

def requiredArgument {α : Type} (decode : Input → Except String α) : Option Input → Except String α
  | some raw => decode raw
  | none => .error "Missing action argument."

def editor
  {α : Type}
  (widget : Model.Editor α)
  (value : α)
  (target : Display.Target)
  (location : Feedback.Location)
  (label : String)
  (disabled : Bool)
  (errors : List Feedback.Error := [])
  : Control α :=
  let input : Display.Editor := match widget with
    | .text => .text value
    | .natural => .natural value
    | .checkbox => .checkbox value
  { invoke := requiredArgument (Input.decode widget)
    view := {
      key := DisplayProtocol.controlKey target, target, label, disabled, location, input
      messages := Feedback.messages errors location } }


def location {raw : Type} {value : raw} : Model.Location raw value → Feedback.Location
  | .self => []
  | @Model.Location.field _ _ inst _ f rest => .field (@Fields.key _ inst _ f) :: location rest
  | @Model.Location.constructor _ _ inst _ c rest => .constructor (@Constructors.key _ inst _ c) :: location rest

def error {raw : Type} {value : raw} (error : Model.Error value) : Feedback.Error where
  message := error.message
  targets := match error.targets with
    | .global => .global
    | .locations first rest => .locations (location first) (rest.map location)

def pathLocation {source target : Type} : Model.Path source target → Feedback.Location
  | .self => []
  | @Model.Path.stepField _ _ _ inst f rest => .field (@Fields.key _ inst _ f) :: pathLocation rest

def Rendered.map {α β : Type} (f : α → β) (rendered : Rendered α) : Rendered β :=
  { rendered with controls := rendered.controls.map (·.map f) }

/-- Picks the branch whose key is the argument; re-choosing the active branch keeps its payload. -/
def choiceControl
  {raw sum : Type}
  (path : Model.Path raw sum)
  (branches : List (Model.Branch sum))
  (value : raw)
  (target : Display.Target)
  (location : Feedback.Location)
  (label : String)
  (disabled : Bool)
  (errors : List Feedback.Error)
  : Control raw :=
  let current := path.get value
  let selected := (branches.find? (·.matches current)).map (·.key)
  { invoke := fun
      | some (.text key) => match branches.find? (·.key == key) with
        | some branch => .ok (if selected == some key then value else path.set branch.start value)
        | none => .error "Unknown option."
      | _ => .error "Expected an option."
    view := {
      key := DisplayProtocol.controlKey target
      target
      label
      disabled
      location
      input := .choice (selected.getD "") (branches.map fun branch => { value := branch.key, label := branch.label })
      messages := Feedback.messages errors location } }

mutual
/-- `location` is where `raw` sits in the form's value. -/
def render
  {raw : Type}
  (component : Model.Component raw)
  (value : raw)
  (errors : List Feedback.Error := [])
  (disabled := false)
  (target : Display.Target := {})
  (location : Feedback.Location := [])
  : Rendered raw :=
  match component with
  | .field path label widget =>
    let control := editor widget (path.get value) target (location ++ pathLocation path) label disabled errors
    let control := control.map (fun replacement => path.set replacement value)
    ⟨.control control.view, [control]⟩
  | .groupOf label children =>
    let children := renderAll children value errors disabled target location 0
    { view := .stack (some label) (children.map (·.view))
      controls := children.flatMap (·.controls) }
  | .computed label computation => ⟨.computed label (computation.eval value), []⟩
  | .visibleWhen condition body =>
    if condition.eval value then render body value errors disabled target location else ⟨.hidden, []⟩
  | .disabledWhen condition body => render body value errors (disabled || condition.eval value) target location
  | .choiceOf path label branches =>
    let location := location ++ pathLocation path
    let selector := choiceControl path branches.toList value target location label disabled errors
    match renderActive branches (path.get value) errors disabled target location 0 with
    | some body =>
      let body := body.map (path.set · value)
      ⟨.stack none [.control selector.view, body.view], selector :: body.controls⟩
    | none => ⟨.control selector.view, [selector]⟩

def renderAll
  {raw : Type}
  (children : Model.Components raw)
  (value : raw)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (index : Nat)
  : List (Rendered raw) :=
  match children with
  | .nil => []
  | .cons head tail =>
    render head value errors disabled (target.child index) location ::
      renderAll tail value errors disabled target location (index + 1)

/-- Renders the body of the branch that `current` was built by, at `target.child index`. -/
def renderActive
  {sum : Type}
  (branches : Model.Branches sum)
  (current : sum)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (index : Nat)
  : Option (Rendered sum) :=
  match branches with
  | .nil => none
  | .cons head tail =>
    match renderBranch head current errors disabled (target.child index) location with
    | some rendered => some rendered
    | none => renderActive tail current errors disabled target location (index + 1)

/-- The branch's body, when `current` was built by its constructor. -/
def renderBranch
  {sum : Type}
  (branch : Model.Branch sum)
  (current : sum)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  : Option (Rendered sum) :=
  match branch with
  | .mk key _ inject project _ body =>
    (project current).map fun payload =>
      (render body payload errors disabled target (location ++ [.constructor key])).map inject
end

end Forms.Runtime.ModelView
