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

def editor {α : Type} (widget : Model.Editor α) (value : α)
    (target : Display.Target) (location : Feedback.Location) (label : String) (disabled : Bool)
    (errors : List Feedback.Error := []) : Control α :=
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
  | @Model.Path.field _ _ _ inst f rest => .field (@Fields.key _ inst _ f) :: pathLocation rest

def render {raw : Type} (component : Model.Component raw) (value : raw)
    (errors : List Feedback.Error := []) (disabled := false) (target : Display.Target := {}) :
    Rendered raw :=
  match component with
  | .field path label widget =>
    let control := (editor widget (path.get value) target (pathLocation path) label disabled errors).map
      (fun replacement => path.set replacement value)
    ⟨.control control.view, [control]⟩
  | .group label children =>
    let children := children.attach.zipIdx.map fun (child, index) =>
      render child.val value errors disabled (target.child index)
    { view := .stack (some label) (children.map (·.view))
      controls := children.flatMap (·.controls) }
  | .computed label computation => ⟨.computed label (computation.eval value), []⟩
  | .visibleWhen condition body =>
    if condition.eval value then render body value errors disabled target else ⟨.hidden, []⟩
  | .disabledWhen condition body => render body value errors (disabled || condition.eval value) target
termination_by sizeOf component
decreasing_by
  all_goals first
    | decreasing_trivial
    | have h := List.sizeOf_lt_of_mem child.property
      simp_wf
      omega

end Forms.Runtime.ModelView
