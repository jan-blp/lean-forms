module

public import Forms.Model.Invocation
public import Forms.Runtime.Input
public import Forms.Runtime.DisplayProtocol

@[expose] public section
namespace Forms.Runtime.ModelView
open Forms.Model

structure Rendered where
  view : Display.View
  controls : List Display.Control

def editor
  {α : Type}
  (widget : Model.Editor α)
  (value : α)
  (target : Display.Target)
  (location : Feedback.Location)
  (label : String)
  (disabled : Bool)
  (errors : List Feedback.Error)
  : Display.Control :=
  let input : Display.Editor := match widget with
    | .text => .text value
    | .natural => .natural value
    | .checkbox => .checkbox value
  { key := DisplayProtocol.controlKey target, target, label, disabled, location, input
    messages := Feedback.messages errors location }

def location {raw : Type} {value : raw} : Model.Location raw value → Feedback.Location
  | .self => []
  | @Model.Location.field _ _ inst _ f rest => .field (@Fields.key _ inst _ f) :: location rest
  | @Model.Location.constructor _ _ inst _ c rest => .constructor (@Constructors.key _ inst _ c) :: location rest
  | .index position rest => .index position.val :: location rest

def error {raw : Type} {value : raw} (error : Model.Error value) : Feedback.Error where
  message := error.message
  targets := match error.targets with
    | .global => .global
    | .locations first rest => .locations (location first) (rest.map location)

def pathLocation {source target : Type} : Model.Path source target → Feedback.Location
  | .self => []
  | @Model.Path.stepField _ _ _ inst f rest => .field (@Fields.key _ inst _ f) :: pathLocation rest

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
  : Display.Control :=
  let selected := (branches.find? (·.matches (path.get value))).map (·.key)
  { key := DisplayProtocol.controlKey target
    target
    label
    disabled
    location
    input := .choice (selected.getD "") (branches.map fun branch =>
      { value := branch.key, label := branch.label })
    messages := Feedback.messages errors location }

def button
  (target : Display.Target)
  (location : Feedback.Location)
  (label : String)
  (disabled : Bool)
  : Display.Control :=
  { key := DisplayProtocol.controlKey target, target, label, disabled, location, input := .action }

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
  : Rendered :=
  match component with
  | .field path label widget =>
    let control := editor widget (path.get value) target (location ++ pathLocation path) label disabled errors
    ⟨.control control, [control]⟩
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
    | some body => ⟨.stack none [.control selector, body.view], selector :: body.controls⟩
    | none => ⟨.control selector, [selector]⟩
  | .list path label itemLabel _ body =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapIdx fun index item =>
      let row := target.child index
      let itemLocation := location ++ [.index index]
      let fields := render body item errors disabled (row.child 0) itemLocation
      let remove := button (row.child 1) itemLocation "Remove" disabled
      (Rendered.mk (.stack (some s!"{itemLabel} {index + 1}") [fields.view, .control remove])
        (fields.controls ++ [remove]))
    let add := button target location s!"Add {itemLabel.toLower}" disabled
    { view := .list label (rows.map (·.view) ++ [.control add]) (Feedback.messages errors location)
      controls := rows.flatMap (·.controls) ++ [add] }

def renderAll
  {raw : Type}
  (children : Model.Components raw)
  (value : raw)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (index : Nat)
  : List Rendered :=
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
  : Option Rendered :=
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
  : Option Rendered :=
  match branch with
  | .mk key _ _ project _ body =>
    (project current).map fun payload =>
      render body payload errors disabled target (location ++ [.constructor key])
end

inductive DecodeError where
  | unknownControl
  | missingArgument
  | unexpectedArgument
  | invalidArgument (message : String)
  | unknownOption
  deriving DecidableEq, Repr

instance : ToString DecodeError where
  toString
    | .unknownControl => "This action is unavailable."
    | .missingArgument => "Missing action argument."
    | .unexpectedArgument => "This action takes no argument."
    | .invalidArgument message => message
    | .unknownOption => "Unknown option."

def noArgument {α : Type} (argument : Option Input) (invocation : α) : Except DecodeError α :=
  match argument with
  | none => .ok invocation
  | some _ => .error .unexpectedArgument

def selectBranch
  {sum : Type}
  (key : String)
  : (branches : Model.Branches sum) → Except DecodeError branches.Invocation
  | .nil => .error .unknownOption
  | .cons (.mk branchKey ..) tail =>
    if branchKey == key then
      .ok (Sum.inl Model.BranchInvocation.select)
    else
      Sum.inr <$> selectBranch key tail

mutual
/-- The invocation of the control `render` puts at `target`. -/
def decode
  {raw : Type}
  (component : Model.Component raw)
  (target : List Nat)
  (argument : Option Input)
  : Except DecodeError component.Invocation :=
  match component, target with
  | .field _ _ widget, [] =>
    match argument with
    | some input => (Input.decode widget input).mapError .invalidArgument
    | none => .error .missingArgument
  | .groupOf _ children, index :: rest => decodeAll children index rest argument
  | .visibleWhen _ body, target => decode body target argument
  | .disabledWhen _ body, target => decode body target argument
  | .choiceOf _ _ branches, [] =>
    match argument with
    | some (.text key) => selectBranch key branches
    | some _ => .error (.invalidArgument "Expected an option.")
    | none => .error .missingArgument
  | .choiceOf _ _ branches, index :: rest => decodeBranches branches index rest argument
  | .list .., [] => noArgument argument Model.ListInvocation.add
  | .list .., [index, 1] => noArgument argument (Model.ListInvocation.remove index)
  | .list _ _ _ _ body, index :: 0 :: rest =>
    Model.ListInvocation.edit index <$> decode body rest argument
  | _, _ => .error .unknownControl

def decodeAll
  {raw : Type}
  (children : Model.Components raw)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  : Except DecodeError children.Invocation :=
  match children, index with
  | .nil, _ => .error .unknownControl
  | .cons head _, 0 => Sum.inl <$> decode head target argument
  | .cons _ tail, index + 1 => Sum.inr <$> decodeAll tail index target argument

def decodeBranch
  {sum : Type}
  (branch : Model.Branch sum)
  (target : List Nat)
  (argument : Option Input)
  : Except DecodeError branch.Invocation :=
  match branch with
  | .mk _ _ _ _ _ body => Model.BranchInvocation.edit <$> decode body target argument

def decodeBranches
  {sum : Type}
  (branches : Model.Branches sum)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  : Except DecodeError branches.Invocation :=
  match branches, index with
  | .nil, _ => .error .unknownControl
  | .cons head _, 0 => Sum.inl <$> decodeBranch head target argument
  | .cons _ tail, index + 1 => Sum.inr <$> decodeBranches tail index target argument
end

def decodeKey
  {raw : Type}
  (component : Model.Component raw)
  (key : ControlKey)
  (argument : Option Input)
  : Except DecodeError component.Invocation :=
  match DisplayProtocol.keyTarget key with
  | some target => decode component target.indices argument
  | none => .error .unknownControl

end Forms.Runtime.ModelView
