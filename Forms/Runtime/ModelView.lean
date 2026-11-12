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

def location {raw : Type} {value : raw} : Model.Location value → Feedback.Location
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
  {Γ : Context}
  {raw sum : Type}
  (path : Model.Path raw sum)
  (branches : List (Model.Branch Γ sum))
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

/-- Lexical binder addresses used only for frontend control keys. -/
abbrev WireScopes := Nat → List Nat

mutual
/-- `location` is where `raw` sits in the form's value; duplicates are kept. -/
def build
  {Γ : Context}
  {raw : Type}
  (state : Model.Env Γ)
  (scopes : WireScopes)
  (component : Model.Component Γ raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (locals : component.LocalState)
  : Display.View :=
  match component with
  | .field path label widget =>
    let location := location ++ pathLocation path
    .control (editor widget (path.get value) target location label disabled errors)
  | .groupOf label children =>
    .stack (some label) (buildAll state scopes children value cache errors disabled target location 0 locals)
  | .computed label computation => .computed label (computation.eval value state)
  | .button label _ => .control {
      key := DisplayProtocol.buttonKey target location
      target, location, label, disabled
      input := .action }
  | .withAvailability availability body =>
    match availability.eval value state with
    | .enabled => build state scopes body value cache errors disabled target location locals
    | .hidden => .hidden
    | .disabled => build state scopes body value cache errors true target location locals
  | .choiceOf path label branches =>
    let location := location ++ pathLocation path
    let selector := choiceControl path branches.toList value target location label disabled errors
    match buildActive state scopes branches (path.get value) cache errors disabled target location 0 locals with
    | some body => .stack none [.control selector, body]
    | none => .control selector
  | .list path label itemLabel _ body =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapIdx fun index item =>
      let row := target.child index
      let itemLocation := location ++ [.index index]
      let fields := build state scopes body item cache errors disabled (row.child 0) itemLocation (locals[index]?.getD body.initialState)
      let remove := button .remove (row.child 1) itemLocation "Remove" disabled
      Display.View.stack (some s!"{itemLabel} {index + 1}") [fields, .control remove]
    let add := button .add target location s!"Add {itemLabel.toLower}" disabled
    .list label (rows ++ [.control add]) (Feedback.messages errors location)
  | @Component.load _ _ _ _inst source body =>
    let status := (source.eval value state).resolve cache
    build state scopes (body status) value cache errors disabled target location (locals.at status (body status).initialState)
  | .table path label itemLabel _ columns selection =>
    let items := path.get value
    let location := location ++ pathLocation path
    let rows := items.mapIdx fun index item =>
      let row := target.child index
      let itemLocation := location ++ [.index index]
      let fields := buildColumns state scopes columns item cache errors disabled (row.child 0) itemLocation 0 (locals[index]?.getD columns.initialState)
      let remove := button .remove (row.child 1) itemLocation "Remove" disabled
      let selected := match selection with
        | .none => none
        | some selected => some (selected.get state == .row index)
      let actions := match selection with
        | none => Display.View.control remove
        | some handle =>
          let select := { button .selectRow (row.child 2) itemLocation
            (if selected.getD false then "Selected" else "Select") disabled with
            key := DisplayProtocol.controlKey .selectRow ((scopes handle.index).map Feedback.Step.index ++ [.index index]) }
          Display.View.stack none [.control select, .control remove]
      ({ label := s!"{itemLabel} {index + 1}", selected, cells := fields ++ [actions] } : Display.TableRow)
    let add := button .add target location s!"Add {itemLabel.toLower}" disabled
    .table label (columns.headers ++ ["Actions"]) rows (.control add) (Feedback.messages errors location)
  | .focus computation body =>
    let path := computation.eval value state
    match path.get? value with
    | none => .hidden
    | some focused =>
      build state scopes body focused cache errors disabled target (location ++ partialPathLocation path) locals
  | .bind _ body =>
    let scopes := fun index => match index with
      | 0 => 1 :: target.indices
      | index + 1 => scopes index
    build (Env.cons locals.value state) scopes body value cache errors disabled (target.child 0) location locals.tail

def buildAll
  {Γ : Context}
  {raw : Type}
  (state : Model.Env Γ)
  (scopes : WireScopes)
  (children : Model.Components Γ raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (index : Nat)
  (locals : children.LocalState)
  : List Display.View :=
  match children with
  | .nil => []
  | .cons head tail =>
    build state scopes head value cache errors disabled (target.child index) location locals.value ::
      buildAll state scopes tail value cache errors disabled target location (index + 1) locals.tail

def buildColumns
  {Γ : Context}
  {raw : Type}
  (state : Model.Env Γ)
  (scopes : WireScopes)
  (children : Model.Columns Γ raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (index : Nat)
  (locals : children.LocalState)
  : List Display.View :=
  match children with
  | .nil => []
  | .cons _ head tail =>
    build state scopes head value cache errors disabled (target.child index) location locals.value ::
      buildColumns state scopes tail value cache errors disabled target location (index + 1) locals.tail

/-- Builds the body of the branch that `current` was built by, at `target.child index`. -/
def buildActive
  {Γ : Context}
  {sum : Type}
  (state : Model.Env Γ)
  (scopes : WireScopes)
  (branches : Model.Branches Γ sum)
  (current : sum)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (index : Nat)
  (locals : branches.LocalState)
  : Option Display.View :=
  match branches with
  | .nil => none
  | .cons head tail =>
    match buildBranch state scopes head current cache errors disabled (target.child index) location locals.value with
    | some view => some view
    | none => buildActive state scopes tail current cache errors disabled target location (index + 1) locals.tail

/-- The branch's body, when `current` was built by its constructor. -/
def buildBranch
  {Γ : Context}
  {sum : Type}
  (state : Model.Env Γ)
  (scopes : WireScopes)
  (branch : Model.Branch Γ sum)
  (current : sum)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (disabled : Bool)
  (target : Display.Target)
  (location : Feedback.Location)
  (locals : branch.LocalState)
  : Option Display.View :=
  match branch with
  | .mk key _ _ project _ body =>
    (project current).map fun payload =>
      build state scopes body payload cache errors disabled target (location ++ [.constructor key]) locals
end

/-- The view of `component`; a control whose key is already shown becomes a note. -/
def render
  {Γ : Context}
  {raw : Type}
  (component : Model.Component Γ raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error := [])
  (state : Model.Env Γ)
  (locals : component.LocalState := component.initialState)
  : Rendered :=
  let view := (build state (fun index => [0, index]) component value cache errors false {} [] locals).dedupe
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
  {Γ : Context} {sum : Type} (state : Model.Env Γ) (key : String)
  (cache : Model.HttpRequest.Cache) (current : sum)
  : (branches : Model.Branches Γ sum) → (locals : branches.LocalState) →
      Except ActionError (branches.ValidInvocation cache current state locals)
  | .nil, _ => .error (.invalid (.unavailableBranch key))
  | .cons (.mk branchKey ..) tail, locals =>
    if branchKey == key then .ok (Sum.inl Model.ValidBranchInvocation.select)
    else Sum.inr <$> selectBranch state key cache current tail locals.tail

def checkedIndex (index length : Nat) : Except ActionError (Fin length) :=
  (Model.checkedIndex index length).mapError .invalid

mutual
/-- The invocation of the control `render` puts at `target`, checked against `current`. -/
def decode
  {Γ : Context}
  {raw : Type}
  (state : Model.Env Γ)
  (component : Model.Component Γ raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (target : List Nat)
  (argument : Option Input)
  (locals : component.LocalState)
  : Except ActionError (component.ValidInvocation cache current state locals) :=
  match component, target with
  | .field _ _ widget, [] =>
    match argument with
    | some input => (Input.decode widget input).mapError .decode
    | none => .error (.decode (.clientBug .missingArgument))
  | .button .., [] => noArgument argument ()
  | .groupOf _ children, index :: rest => decodeAll state children cache current index rest argument locals
  | .withAvailability availability body, target => do
    let invocation ← decode state body cache current target argument locals
    match h : availability.eval current state with
    | .enabled => return ⟨invocation, h⟩
    | .hidden => throw (.invalid .hidden)
    | .disabled => throw (.invalid .disabled)
  | .choiceOf path _ branches, [] =>
    match argument with
    | some (.text key) => selectBranch state key cache (path.get current) branches locals
    | some _ => .error (.decode (.clientBug (.wrongArgument "an option")))
    | none => .error (.decode (.clientBug .missingArgument))
  | .choiceOf path _ branches, index :: rest =>
    decodeBranches state branches cache (path.get current) index rest argument locals
  | .list .., [] => noArgument argument Model.ValidListInvocation.add
  | .list path .., [index, 1] => do
    let index ← checkedIndex index (path.get current).length
    noArgument argument (Model.ValidListInvocation.remove index)
  | .list path _ _ _ body, index :: 0 :: rest => do
    let items := path.get current
    let index ← checkedIndex index items.length
    Model.ValidListInvocation.edit index <$> decode state body cache (items.get index) rest argument (locals[index.val]?.getD body.initialState)
  | @Component.load _ _ _ _inst source body, target =>
    let status := (source.eval current state).resolve cache
    decode state (body status) cache current target argument (locals.at status (body status).initialState)
  | .table .., [] => noArgument argument Model.ValidTableInvocation.add
  | .table path .., [index, 1] => do
    let index ← checkedIndex index (path.get current).length
    noArgument argument (Model.ValidTableInvocation.remove index)
  | .table path _ _ _ columns _, index :: 0 :: column :: rest => do
    let items := path.get current
    let index ← checkedIndex index items.length
    Model.ValidTableInvocation.edit index <$> decodeColumns state columns cache (items.get index) column rest argument (locals[index.val]?.getD columns.initialState)
  | .table path _ _ _ _ (some _), [index, 2] => do
    let index ← checkedIndex index (path.get current).length
    noArgument argument (.select rfl index)
  | .focus computation body, target =>
    match present : (computation.eval current state).get? current with
    | none => .error (.invalid .absent)
    | some value => do
      return ⟨value, present, ← decode state body cache value target argument locals⟩
  | .bind _ body, 0 :: rest =>
    decode (Env.cons locals.value state) body cache current rest argument locals.tail
  | _, _ => .error (.decode (.clientBug .unknownControl))

def decodeAll
  {Γ : Context}
  {raw : Type}
  (state : Model.Env Γ)
  (children : Model.Components Γ raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  (locals : children.LocalState)
  : Except ActionError (children.ValidInvocation cache current state locals) :=
  match children, index with
  | .nil, _ => .error (.decode (.clientBug .unknownControl))
  | .cons head _, 0 => Sum.inl <$> decode state head cache current target argument locals.value
  | .cons _ tail, index + 1 => Sum.inr <$> decodeAll state tail cache current index target argument locals.tail

def decodeColumns
  {Γ : Context}
  {raw : Type}
  (state : Model.Env Γ)
  (children : Model.Columns Γ raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  (locals : children.LocalState)
  : Except ActionError (children.ValidInvocation cache current state locals) :=
  match children, index with
  | .nil, _ => .error (.decode (.clientBug .unknownControl))
  | .cons _ head _, 0 => Sum.inl <$> decode state head cache current target argument locals.value
  | .cons _ _ tail, index + 1 => Sum.inr <$> decodeColumns state tail cache current index target argument locals.tail

def decodeBranch
  {Γ : Context}
  {sum : Type}
  (state : Model.Env Γ)
  (branch : Model.Branch Γ sum)
  (cache : Model.HttpRequest.Cache)
  (current : sum)
  (target : List Nat)
  (argument : Option Input)
  (locals : branch.LocalState)
  : Except ActionError (branch.ValidInvocation cache current state locals) :=
  match branch with
  | .mk _ _ _ project _ body =>
    match active : project current with
    | some payload =>
      Model.ValidBranchInvocation.edit payload active <$> decode state body cache payload target argument locals
    | none => .error (.invalid .inactiveBranch)

def decodeBranches
  {Γ : Context}
  {sum : Type}
  (state : Model.Env Γ)
  (branches : Model.Branches Γ sum)
  (cache : Model.HttpRequest.Cache)
  (current : sum)
  (index : Nat)
  (target : List Nat)
  (argument : Option Input)
  (locals : branches.LocalState)
  : Except ActionError (branches.ValidInvocation cache current state locals) :=
  match branches, index with
  | .nil, _ => .error (.decode (.clientBug .unknownControl))
  | .cons head _, 0 => Sum.inl <$> decodeBranch state head cache current target argument locals.value
  | .cons _ tail, index + 1 => Sum.inr <$> decodeBranches state tail cache current index target argument locals.tail
end

def decodeKey
  {Γ : Context}
  {raw : Type}
  (component : Model.Component Γ raw)
  (cache : Model.HttpRequest.Cache)
  (current : raw)
  (key : ControlKey)
  (argument : Option Input)
  (state : Model.Env Γ)
  (locals : component.LocalState := component.initialState)
  : Except ActionError (component.ValidInvocation cache current state locals) :=
  match ((render component current cache [] state locals).controls.find? (·.key == key)) with
  | some control => decode state component cache current control.target.indices argument locals
  | none => .error (.invalid .absent)

end Forms.Runtime.ModelView
