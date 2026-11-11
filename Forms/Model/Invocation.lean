module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model

inductive ValidListInvocation (length : Nat) (valid : Fin length → Type) where
  | add
  | remove (index : Fin length)
  | edit (index : Fin length) (invocation : valid index)

inductive ValidTableInvocation (length : Nat) (valid : Fin length → Type) (selectable : Bool) where
  | add
  | remove (index : Fin length)
  | edit (index : Fin length) (invocation : valid index)
  | select (enabled : selectable = true) (index : Fin length)

/-- An invocation checked against the value reached by the current partial path. -/
structure ValidFocusInvocation {item : Type} (found : Option item) (valid : item → Type) where
  value : item
  present : found = some value
  invocation : valid value

/-- A branch invocation checked against `current`, the active payload if this branch is active. -/
inductive ValidBranchInvocation
    {payload : Type}
    (current : Option payload)
    (valid : payload → Type)
    : Type where
  | select
  | edit (payload : payload) (active : current = some payload) (invocation : valid payload)

/-- Why an invocation does not apply to the current value. -/
inductive InvocationError where
  | hidden
  | disabled
  | inactiveBranch
  | indexOutOfBounds (index length : Nat)
  /-- No control with the key is shown. -/
  | absent
  /-- The choice has no branch with the requested key. -/
  | unavailableBranch (key : String)
  deriving DecidableEq, Repr

instance : ToString InvocationError where
  toString
    | .hidden => "This action is unavailable: the control is hidden."
    | .disabled => "This action is unavailable: the control is disabled."
    | .inactiveBranch => "This action is unavailable: the option is not selected."
    | .indexOutOfBounds index length =>
      s!"This action is unavailable: item {index + 1} of {length}."
    | .absent => "This action is unavailable: the control is no longer shown."
    | .unavailableBranch key => s!"This action is unavailable: branch '{key}' is no longer available."

mutual
/-- Invocations checked against the current model, UI state, and loaded responses. -/
def Component.ValidInvocation {raw : Type} (component : Component raw) (cache : HttpRequest.Cache)
    (current : raw) (state : UiState := {}) : Type :=
  match component with
  | @Component.field _ value .. => value
  | .groupOf _ children => children.ValidInvocation cache current state
  | .computed .. => Empty
  | .withAvailability availability body =>
    { _invocation : body.ValidInvocation cache current state // availability.eval current state = .enabled }
  | .choiceOf path _ branches => branches.ValidInvocation cache (path.get current) state
  | .list path _ _ _ body =>
    ValidListInvocation (path.get current).length fun index =>
      body.ValidInvocation cache ((path.get current).get index) state
  | .table path _ _ _ columns selection =>
    let items := path.get current
    ValidTableInvocation items.length (fun index => columns.ValidInvocation cache (items.get index) state)
      selection.isSome
  | .focus target body =>
    ValidFocusInvocation ((target.eval current state).get? current) (fun value => body.ValidInvocation cache value state)
  | .load source body =>
    (body ((source.eval current state).resolve cache)).ValidInvocation cache current state

def Components.ValidInvocation {raw : Type} (children : Components raw) (cache : HttpRequest.Cache)
    (current : raw) (state : UiState := {}) : Type :=
  match children with
  | .nil => Empty
  | .cons head tail =>
    head.ValidInvocation cache current state ⊕ tail.ValidInvocation cache current state

def Columns.ValidInvocation {raw : Type} (columns : Columns raw) (cache : HttpRequest.Cache)
    (current : raw) (state : UiState := {}) : Type :=
  match columns with
  | .nil => Empty
  | .cons _ head tail =>
    head.ValidInvocation cache current state ⊕ tail.ValidInvocation cache current state

def Branch.ValidInvocation {sum : Type} (branch : Branch sum) (cache : HttpRequest.Cache)
    (current : sum) (state : UiState := {}) : Type :=
  match branch with
  | .mk _ _ _ project _ body =>
    ValidBranchInvocation (project current) fun payload => body.ValidInvocation cache payload state

def Branches.ValidInvocation {sum : Type} (branches : Branches sum) (cache : HttpRequest.Cache)
    (current : sum) (state : UiState := {}) : Type :=
  match branches with
  | .nil => Empty
  | .cons head tail =>
    head.ValidInvocation cache current state ⊕ tail.ValidInvocation cache current state
end

def checkedIndex (index length : Nat) : Except InvocationError (Fin length) :=
  if h : index < length then
    .ok ⟨index, h⟩
  else
    .error (.indexOutOfBounds index length)

/-- The model and UI state after a checked invocation. -/
structure ComponentUpdate (raw : Type) where
  value : raw
  state : UiState

def ComponentUpdate.mapValue {source target : Type} (update : ComponentUpdate source)
    (f : source → target) : ComponentUpdate target :=
  { value := f update.value, state := update.state }

mutual
def Component.applyValid {raw : Type} (component : Component raw) (cache : HttpRequest.Cache)
    (current : raw) (state : UiState) (invocation : component.ValidInvocation cache current state)
    : ComponentUpdate raw :=
  match component, invocation with
  | .field path .., value => ⟨path.set value current, state⟩
  | .groupOf _ children, invocation => children.applyValid cache current state invocation
  | .computed .., invocation => nomatch invocation
  | .withAvailability _ body, invocation => body.applyValid cache current state invocation.val
  | .choiceOf path _ branches, invocation =>
    (branches.applyValid cache (path.get current) state invocation).mapValue (fun value => path.set value current)
  | .list path _ _ initial body, invocation =>
    let items := path.get current
    let Valid index := body.ValidInvocation cache (items.get index) state
    match (invocation : ValidListInvocation items.length Valid) with
    | .add => ⟨path.set (items ++ [initial]) current, state⟩
    | .remove index => ⟨path.set (items.eraseIdx index) current, state⟩
    | .edit index invocation =>
      (body.applyValid cache (items.get index) state invocation).mapValue fun value =>
        path.set (items.set index value) current
  | .load source body, invocation =>
    (body ((source.eval current state).resolve cache)).applyValid cache current state invocation
  | .table path _ _ initial columns selection, invocation =>
    let items := path.get current
    let Valid index := columns.ValidInvocation cache (items.get index) state
    match (invocation : ValidTableInvocation items.length Valid selection.isSome) with
    | .add => ⟨path.set (items ++ [initial]) current, state⟩
    | .remove index =>
      let next := path.set (items.eraseIdx index) current
      let state := match selection with
        | none => state
        | some selected => selected.set ((selected.get state).remove index.val) state
      ⟨next, state⟩
    | .edit index invocation =>
      (columns.applyValid cache (items.get index) state invocation).mapValue fun value =>
        path.set (items.set index value) current
    | .select enabled index =>
      match selection with
      | none => nomatch enabled
      | some selected => ⟨current, selected.set (.row index.val) state⟩
  | .focus target body, invocation =>
    (body.applyValid cache invocation.value state invocation.invocation).mapValue fun value =>
      (target.eval current state).set value current

def Components.applyValid {raw : Type} (children : Components raw) (cache : HttpRequest.Cache)
    (current : raw) (state : UiState) (invocation : children.ValidInvocation cache current state)
    : ComponentUpdate raw :=
  match children, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.ValidInvocation cache current state ⊕ tail.ValidInvocation cache current state) with
    | .inl invocation => head.applyValid cache current state invocation
    | .inr invocation => tail.applyValid cache current state invocation

def Columns.applyValid {raw : Type} (columns : Columns raw) (cache : HttpRequest.Cache)
    (current : raw) (state : UiState) (invocation : columns.ValidInvocation cache current state)
    : ComponentUpdate raw :=
  match columns, invocation with
  | .nil, invocation => nomatch invocation
  | .cons _ head tail, invocation =>
    match (invocation : head.ValidInvocation cache current state ⊕ tail.ValidInvocation cache current state) with
    | .inl invocation => head.applyValid cache current state invocation
    | .inr invocation => tail.applyValid cache current state invocation

/-- Re-selecting the active branch keeps its payload. -/
def Branch.applyValid {sum : Type} (branch : Branch sum) (cache : HttpRequest.Cache)
    (current : sum) (state : UiState) (invocation : branch.ValidInvocation cache current state)
    : ComponentUpdate sum :=
  match branch with
  | .mk _ _ inject project initial body =>
    let Valid payload := body.ValidInvocation cache payload state
    match (invocation : ValidBranchInvocation (project current) Valid) with
    | .select => ⟨if (project current).isSome then current else inject initial, state⟩
    | .edit payload _ invocation => (body.applyValid cache payload state invocation).mapValue inject

def Branches.applyValid {sum : Type} (branches : Branches sum) (cache : HttpRequest.Cache)
    (current : sum) (state : UiState) (invocation : branches.ValidInvocation cache current state)
    : ComponentUpdate sum :=
  match branches, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.ValidInvocation cache current state ⊕ tail.ValidInvocation cache current state) with
    | .inl invocation => head.applyValid cache current state invocation
    | .inr invocation => tail.applyValid cache current state invocation
end

end Forms.Model
