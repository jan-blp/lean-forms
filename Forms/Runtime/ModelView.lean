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

def partialPathLocation {source target : Type} : Model.PartialPath source target → Feedback.Location
  | .self => []
  | .empty => []
  | @Model.PartialPath.field _ _ _ inst f rest =>
    .field (@Fields.key _ inst _ f) :: partialPathLocation rest
  | @Model.PartialPath.constructor _ _ _ inst _ ctor rest =>
    .constructor (@Constructors.key _ inst _ ctor) :: partialPathLocation rest
  | .index position rest => .index position :: partialPathLocation rest

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
  (state : Model.UiState)
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
    .stack (some label) (buildAll state children value cache errors disabled target location 0)
  | .computed label computation => .computed label (computation.eval value state)
  | .withAvailability availability body =>
    match availability.eval value state with
    | .enabled => build state body value cache errors disabled target location
    | .hidden => .hidden
    | .disabled => build state body value cache errors true target location
  | .choiceOf path label branches =>
    let location := location ++ pathLocation path
    let selector := choiceControl path branches.toList value target location label disabled errors
    match buildActive state branches (path.get value) cache errors disabled target location 0 with
    | some body => .stack none [.control selector, body]
    | none => .control selector
  | .list path label itemLabel _ body =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapIdx fun index item =>
      let row := target.child index
      let itemLocation := location ++ [.index index]
      let fields := build state body item cache errors disabled (row.child 0) itemLocation
      let remove := button .remove (row.child 1) itemLocation "Remove" disabled
      Display.View.stack (some s!"{itemLabel} {index + 1}") [fields, .control remove]
    let add := button .add target location s!"Add {itemLabel.toLower}" disabled
    .list label (rows ++ [.control add]) (Feedback.messages errors location)
  | .load source body =>
    build state (body ((source.eval value state).resolve cache)) value cache errors disabled target location
  | .table path label itemLabel _ columns selection =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapIdx fun index item =>
      let row := target.child index
      let itemLocation := location ++ [.index index]
      let fields := buildColumns state columns item cache errors disabled (row.child 0) itemLocation 0
      let remove := button .remove (row.child 1) itemLocation "Remove" disabled
      let selected := match selection with
        | .none => none
        | some selected => some (selected.get state == .row index)
      let actions := match selection with
        | none => Display.View.control remove
        | some handle =>
          let select := { button .selectRow (row.child 2) itemLocation
            (if selected.getD false then "Selected" else "Select") disabled with
            key := DisplayProtocol.controlKey .selectRow [.field handle.key, .index index] }
          Display.View.stack none [.control select, .control remove]
      ({ label := s!"{itemLabel} {index + 1}", selected, cells := fields ++ [actions] } : Display.TableRow)
    let add := button .add target location s!"Add {itemLabel.toLower}" disabled
    .table label (columns.headers ++ ["Actions"]) rows (.control add) (Feedback.messages errors location)
  | .focus computation body =>
    let path := computation.eval value state
    match path.get? value with
    | none => .hidden
    | some focused =>
      build state body focused cache errors disabled target (location ++ partialPathLocation path)

def buildAll
  {raw : Type}
  (state : Model.UiState)
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
    build state head value cache errors disabled (target.child index) location ::
      buildAll state tail value cache errors disabled target location (index + 1)

def buildColumns
  {raw : Type}
  (state : Model.UiState)
  (children : Model.Columns raw)
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
  | .cons _ head tail =>
    build state head value cache errors disabled (target.child index) location ::
      buildColumns state tail value cache errors disabled target location (index + 1)

/-- Builds the body of the branch that `current` was built by, at `target.child index`. -/
def buildActive
  {sum : Type}
  (state : Model.UiState)
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
    match buildBranch state head current cache errors disabled (target.child index) location with
    | some view => some view
    | none => buildActive state tail current cache errors disabled target location (index + 1)

/-- The branch's body, when `current` was built by its constructor. -/
def buildBranch
  {sum : Type}
  (state : Model.UiState)
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
      build state body payload cache errors disabled target (location ++ [.constructor key])
end

/-- The view of `component`; a control whose key is already shown becomes a note. -/
def render
  {raw : Type}
  (component : Model.Component raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error := [])
  (state : Model.UiState := {})
  : Rendered :=
  let view := (build state component value cache errors false {} []).dedupe
  ⟨view, view.controls⟩

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
  (state : Model.UiState)
  (key : String)
  (cache : Model.HttpRequest.Cache)
  (current : sum)
  : (branches : Model.Branches sum) → Except ActionError (branches.ValidInvocation cache current state)
  | .nil => .error (.invalid (.unavailableBranch key))
  | .cons (.mk branchKey ..) tail =>
    if branchKey == key then
      .ok (Sum.inl Model.ValidBranchInvocation.select)
    else
      Sum.inr <$> selectBranch state key cache current tail

def checkedIndex (index length : Nat) : Except ActionError (Fin length) :=
  (Model.checkedIndex index length).mapError .invalid

mutual
/-- The invocation of the control `render` puts at `target`, checked against `current`. -/
def decode
  {raw : Type}
  (state : Model.UiState)
  (component : Model.Component raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (target : List Nat)
  (argument : Option Input)
  : Except ActionError (component.ValidInvocation cache current state) :=
  match component, target with
  | .field _ _ widget, [] =>
    match argument with
    | some input => (Input.decode widget input).mapError .decode
    | none => .error (.decode (.clientBug .missingArgument))
  | .groupOf _ children, index :: rest => decodeAll state children cache current index rest argument
  | .withAvailability availability body, target => do
    let invocation ← decode state body cache current target argument
    match h : availability.eval current state with
    | .enabled => return ⟨invocation, h⟩
    | .hidden => throw (.invalid .hidden)
    | .disabled => throw (.invalid .disabled)
  | .choiceOf path _ branches, [] =>
    match argument with
    | some (.text key) => selectBranch state key cache (path.get current) branches
    | some _ => .error (.decode (.clientBug (.wrongArgument "an option")))
    | none => .error (.decode (.clientBug .missingArgument))
  | .choiceOf path _ branches, index :: rest =>
    decodeBranches state branches cache (path.get current) index rest argument
  | .list .., [] => noArgument argument Model.ValidListInvocation.add
  | .list path .., [index, 1] => do
    let index ← checkedIndex index (path.get current).length
    noArgument argument (Model.ValidListInvocation.remove index)
  | .list path _ _ _ body, index :: 0 :: rest => do
    let items := path.get current
    let index ← checkedIndex index items.length
    Model.ValidListInvocation.edit index <$> decode state body cache (items.get index) rest argument
  | .load source body, target =>
    decode state (body ((source.eval current state).resolve cache)) cache current target argument
  | .table .., [] => noArgument argument Model.ValidTableInvocation.add
  | .table path .., [index, 1] => do
    let index ← checkedIndex index (path.get current).length
    noArgument argument (Model.ValidTableInvocation.remove index)
  | .table path _ _ _ columns _, index :: 0 :: column :: rest => do
    let items := path.get current
    let index ← checkedIndex index items.length
    Model.ValidTableInvocation.edit index <$> decodeColumns state columns cache (items.get index) column rest argument
  | .table path _ _ _ _ (some _), [index, 2] => do
    let index ← checkedIndex index (path.get current).length
    noArgument argument (.select rfl index)
  | .focus computation body, target =>
    match present : (computation.eval current state).get? current with
    | none => .error (.invalid .absent)
    | some value => do
      return ⟨value, present, ← decode state body cache value target argument⟩
  | _, _ => .error (.decode (.clientBug .unknownControl))

def decodeAll
  {raw : Type}
  (state : Model.UiState)
  (children : Model.Components raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  : Except ActionError (children.ValidInvocation cache current state) :=
  match children, index with
  | .nil, _ => .error (.decode (.clientBug .unknownControl))
  | .cons head _, 0 => Sum.inl <$> decode state head cache current target argument
  | .cons _ tail, index + 1 => Sum.inr <$> decodeAll state tail cache current index target argument

def decodeColumns
  {raw : Type}
  (state : Model.UiState)
  (children : Model.Columns raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  : Except ActionError (children.ValidInvocation cache current state) :=
  match children, index with
  | .nil, _ => .error (.decode (.clientBug .unknownControl))
  | .cons _ head _, 0 => Sum.inl <$> decode state head cache current target argument
  | .cons _ _ tail, index + 1 => Sum.inr <$> decodeColumns state tail cache current index target argument

def decodeBranch
  {sum : Type}
  (state : Model.UiState)
  (branch : Model.Branch sum)
  (cache : Model.HttpRequest.Cache)
  (current : sum)
  (target : List Nat)
  (argument : Option Input)
  : Except ActionError (branch.ValidInvocation cache current state) :=
  match branch with
  | .mk _ _ _ project _ body =>
    match active : project current with
    | some payload =>
      Model.ValidBranchInvocation.edit payload active <$> decode state body cache payload target argument
    | none => .error (.invalid .inactiveBranch)

def decodeBranches
  {sum : Type}
  (state : Model.UiState)
  (branches : Model.Branches sum)
  (cache : Model.HttpRequest.Cache)
  (current : sum)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  : Except ActionError (branches.ValidInvocation cache current state) :=
  match branches, index with
  | .nil, _ => .error (.decode (.clientBug .unknownControl))
  | .cons head _, 0 => Sum.inl <$> decodeBranch state head cache current target argument
  | .cons _ tail, index + 1 => Sum.inr <$> decodeBranches state tail cache current index target argument
end

def decodeKey
  {raw : Type}
  (component : Model.Component raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (key : ControlKey)
  (argument : Option Input)
  (state : Model.UiState := {})
  : Except ActionError (component.ValidInvocation cache current state) :=
  match ((render component current cache [] state).controls.find? (·.key == key)) with
  | some control => decode state component cache current control.target.indices argument
  | none => .error (.invalid .absent)

end Forms.Runtime.ModelView
