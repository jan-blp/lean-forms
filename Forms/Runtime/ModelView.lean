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
  { key := DisplayProtocol.controlKey .edit location, target, label, disabled, location, input
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
  { key := DisplayProtocol.controlKey .select location
    target
    label
    disabled
    location
    input := .choice (selected.getD "") (branches.map fun branch =>
      { value := branch.key, label := branch.label })
    messages := Feedback.messages errors location }

def button
  (action : DisplayProtocol.Action)
  (target : Display.Target)
  (location : Feedback.Location)
  (label : String)
  (disabled : Bool)
  : Display.Control :=
  { key := DisplayProtocol.controlKey action location, target, label, disabled, location
    input := .action }

mutual
/-- `location` is where `raw` sits in the form's value; duplicates are kept. -/
def build
  {raw : Type}
  (component : Model.Component raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  : Display.View :=
  match component with
  | .field path label widget =>
    let location := location ++ pathLocation path
    .control (editor widget (path.get value) target location label disabled errors)
  | .groupOf label children =>
    .stack (some label) (buildAll children value cache errors disabled target location 0)
  | .computed label computation => .computed label (computation.eval value)
  | .visibleWhen condition body =>
    if condition.eval value then build body value cache errors disabled target location
    else .hidden
  | .disabledWhen condition body =>
    build body value cache errors (disabled || condition.eval value) target location
  | .choiceOf path label branches =>
    let location := location ++ pathLocation path
    let selector := choiceControl path branches.toList value target location label disabled errors
    match buildActive branches (path.get value) cache errors disabled target location 0 with
    | some body => .stack none [.control selector, body]
    | none => .control selector
  | .list path label itemLabel _ body =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapIdx fun index item =>
      let row := target.child index
      let itemLocation := location ++ [.index index]
      let fields := build body item cache errors disabled (row.child 0) itemLocation
      let remove := button .remove (row.child 1) itemLocation "Remove" disabled
      Display.View.stack (some s!"{itemLabel} {index + 1}") [fields, .control remove]
    let add := button .add target location s!"Add {itemLabel.toLower}" disabled
    .list label (rows ++ [.control add]) (Feedback.messages errors location)
  | .load source body =>
    build (body ((source.eval value).resolve cache)) value cache errors disabled target location

def buildAll
  {raw : Type}
  (children : Model.Components raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (index : Nat)
  : List Display.View :=
  match children with
  | .nil => []
  | .cons head tail =>
    build head value cache errors disabled (target.child index) location ::
      buildAll tail value cache errors disabled target location (index + 1)

/-- Builds the body of the branch that `current` was built by, at `target.child index`. -/
def buildActive
  {sum : Type}
  (branches : Model.Branches sum)
  (current : sum)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (index : Nat)
  : Option Display.View :=
  match branches with
  | .nil => none
  | .cons head tail =>
    match buildBranch head current cache errors disabled (target.child index) location with
    | some view => some view
    | none => buildActive tail current cache errors disabled target location (index + 1)

/-- The branch's body, when `current` was built by its constructor. -/
def buildBranch
  {sum : Type}
  (branch : Model.Branch sum)
  (current : sum)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  : Option Display.View :=
  match branch with
  | .mk key _ _ project _ body =>
    (project current).map fun payload =>
      build body payload cache errors disabled target (location ++ [.constructor key])
end

/-- The view of `component`; a control whose key is already shown becomes a note. -/
def render
  {raw : Type}
  (component : Model.Component raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error := [])
  : Rendered :=
  let view := (build component value cache errors false {} []).dedupe
  ⟨view, view.controls⟩

/-- No two controls `render` shows share a key, so a key names at most one control. -/
theorem render_keys_nodup
  {raw : Type}
  (component : Model.Component raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  : ((render component value cache errors).controls.map (·.key)).Nodup :=
  Display.View.dedupe_keys_nodup _

/-- Why a control key and argument name no invocation that applies. -/
inductive ActionError where
  | decode (error : DecodeError)
  | invalid (error : Model.InvocationError)

def noArgument {α : Type} (argument : Option Input) (invocation : α) : Except ActionError α :=
  match argument with
  | none => .ok invocation
  | some _ => .error (.decode (.clientBug .unexpectedArgument))

def selectBranch
  {sum : Type}
  (key : String)
  (cache : Model.HttpRequest.Cache)
  (current : sum)
  : (branches : Model.Branches sum) → Except ActionError (branches.ValidInvocation cache current)
  | .nil => .error (.decode (.clientBug .unknownOption))
  | .cons (.mk branchKey ..) tail =>
    if branchKey == key then
      .ok (Sum.inl Model.ValidBranchInvocation.select)
    else
      Sum.inr <$> selectBranch key cache current tail

def checkedIndex (index length : Nat) : Except ActionError (Fin length) :=
  (Model.checkedIndex index length).mapError .invalid

mutual
/-- The invocation of the control `render` puts at `target`, checked against `current`. -/
def decode
  {raw : Type}
  (component : Model.Component raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (target : List Nat)
  (argument : Option Input)
  : Except ActionError (component.ValidInvocation cache current) :=
  match component, target with
  | .field _ _ widget, [] =>
    match argument with
    | some input => (Input.decode widget input).mapError .decode
    | none => .error (.decode (.clientBug .missingArgument))
  | .groupOf _ children, index :: rest => decodeAll children cache current index rest argument
  | .visibleWhen condition body, target => do
    let invocation ← decode body cache current target argument
    if h : condition.eval current = true then
      return ⟨invocation, h⟩
    else
      throw (.invalid .hidden)
  | .disabledWhen condition body, target => do
    let invocation ← decode body cache current target argument
    if h : condition.eval current = false then
      return ⟨invocation, h⟩
    else
      throw (.invalid .disabled)
  | .choiceOf path _ branches, [] =>
    match argument with
    | some (.text key) => selectBranch key cache (path.get current) branches
    | some _ => .error (.decode (.clientBug (.wrongArgument "an option")))
    | none => .error (.decode (.clientBug .missingArgument))
  | .choiceOf path _ branches, index :: rest =>
    decodeBranches branches cache (path.get current) index rest argument
  | .list .., [] => noArgument argument Model.ValidListInvocation.add
  | .list path .., [index, 1] => do
    let index ← checkedIndex index (path.get current).length
    noArgument argument (Model.ValidListInvocation.remove index)
  | .list path _ _ _ body, index :: 0 :: rest => do
    let items := path.get current
    let index ← checkedIndex index items.length
    Model.ValidListInvocation.edit index <$> decode body cache (items.get index) rest argument
  | .load source body, target =>
    decode (body ((source.eval current).resolve cache)) cache current target argument
  | _, _ => .error (.decode (.clientBug .unknownControl))

def decodeAll
  {raw : Type}
  (children : Model.Components raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  : Except ActionError (children.ValidInvocation cache current) :=
  match children, index with
  | .nil, _ => .error (.decode (.clientBug .unknownControl))
  | .cons head _, 0 => Sum.inl <$> decode head cache current target argument
  | .cons _ tail, index + 1 => Sum.inr <$> decodeAll tail cache current index target argument

def decodeBranch
  {sum : Type}
  (branch : Model.Branch sum)
  (cache : Model.HttpRequest.Cache)
  (current : sum)
  (target : List Nat)
  (argument : Option Input)
  : Except ActionError (branch.ValidInvocation cache current) :=
  match branch with
  | .mk _ _ _ project _ body =>
    match active : project current with
    | some payload =>
      Model.ValidBranchInvocation.edit payload active <$> decode body cache payload target argument
    | none => .error (.invalid .inactiveBranch)

def decodeBranches
  {sum : Type}
  (branches : Model.Branches sum)
  (cache : Model.HttpRequest.Cache)
  (current : sum)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  : Except ActionError (branches.ValidInvocation cache current) :=
  match branches, index with
  | .nil, _ => .error (.decode (.clientBug .unknownControl))
  | .cons head _, 0 => Sum.inl <$> decodeBranch head cache current target argument
  | .cons _ tail, index + 1 => Sum.inr <$> decodeBranches tail cache current index target argument
end

def decodeKey
  {raw : Type}
  (component : Model.Component raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (key : ControlKey)
  (argument : Option Input)
  : Except ActionError (component.ValidInvocation cache current) :=
  match ((render component current cache).controls.find? (·.key == key)) with
  | some control => decode component cache current control.target.indices argument
  | none => .error (.invalid .absent)

end Forms.Runtime.ModelView
