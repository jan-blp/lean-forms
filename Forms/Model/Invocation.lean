module

public import Forms.Model.Component.LocalState

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
/-- Invocations checked against the current model, context, and localType bindings. -/
def Component.ValidInvocation {Γ : Context} {raw : Type} (component : Component Γ raw) (cache : HttpRequest.Cache)
    (current : raw) (state : Env Γ) (locals : component.LocalState := component.initialState) : Type :=
  match component with
  | @Component.field _ _ value .. => value
  | .groupOf _ children => children.ValidInvocation cache current state locals
  | .computed .. => Empty
  | .button .. => Unit
  | .withAvailability availability body =>
    { _invocation : body.ValidInvocation cache current state locals // availability.eval current state = .enabled }
  | .choiceOf path _ branches => branches.ValidInvocation cache (path.get current) state locals
  | .list path _ _ _ body =>
    ValidListInvocation (path.get current).length fun index =>
      body.ValidInvocation cache ((path.get current).get index) state (locals[index.val]?.getD body.initialState)
  | .table path _ _ _ columns selection =>
    let items := path.get current
    ValidTableInvocation items.length (fun index => columns.ValidInvocation cache (items.get index) state
      (locals[index.val]?.getD columns.initialState)) selection.isSome
  | .focus target body =>
    ValidFocusInvocation ((target.eval current state).get? current) (fun value => body.ValidInvocation cache value state locals)
  | .bind _ body => body.ValidInvocation cache current (Env.cons locals.value state) locals.tail
  | @Component.load _ _ _ _inst source body =>
    let status := (source.eval current state).resolve cache
    (body status).ValidInvocation cache current state (locals.at status (body status).initialState)

def Components.ValidInvocation {Γ : Context} {raw : Type} (children : Components Γ raw) (cache : HttpRequest.Cache)
    (current : raw) (state : Env Γ) (locals : children.LocalState := children.initialState) : Type :=
  match children with
  | .nil => Empty
  | .cons head tail =>
    head.ValidInvocation cache current state locals.value ⊕ tail.ValidInvocation cache current state locals.tail

def Columns.ValidInvocation {Γ : Context} {raw : Type} (columns : Columns Γ raw) (cache : HttpRequest.Cache)
    (current : raw) (state : Env Γ) (locals : columns.LocalState := columns.initialState) : Type :=
  match columns with
  | .nil => Empty
  | .cons _ head tail =>
    head.ValidInvocation cache current state locals.value ⊕ tail.ValidInvocation cache current state locals.tail

def Branch.ValidInvocation {Γ : Context} {sum : Type} (branch : Branch Γ sum) (cache : HttpRequest.Cache)
    (current : sum) (state : Env Γ) (locals : branch.LocalState := branch.initialState) : Type :=
  match branch with
  | .mk _ _ _ project _ body =>
    ValidBranchInvocation (project current) fun payload => body.ValidInvocation cache payload state locals

def Branches.ValidInvocation {Γ : Context} {sum : Type} (branches : Branches Γ sum) (cache : HttpRequest.Cache)
    (current : sum) (state : Env Γ) (locals : branches.LocalState := branches.initialState) : Type :=
  match branches with
  | .nil => Empty
  | .cons head tail =>
    head.ValidInvocation cache current state locals.value ⊕ tail.ValidInvocation cache current state locals.tail
end

def checkedIndex (index length : Nat) : Except InvocationError (Fin length) :=
  if h : index < length then
    .ok ⟨index, h⟩
  else
    .error (.indexOutOfBounds index length)

/-- The model, context, and localType bindings after a checked invocation. -/
structure ComponentUpdate (Γ : Context) (raw localType : Type) where
  value : raw
  state : Env Γ
  locals : localType

def ComponentUpdate.mapValue {Γ : Context} {source target localType : Type}
    (update : ComponentUpdate Γ source localType) (f : source → target) : ComponentUpdate Γ target localType :=
  { update with value := f update.value }

def ComponentUpdate.mapLocals {Γ : Context} {raw before after : Type}
    (update : ComponentUpdate Γ raw before) (f : before → after) : ComponentUpdate Γ raw after :=
  { update with locals := f update.locals }

mutual
def Component.applyValid {Γ : Context} {raw : Type} (component : Component Γ raw) (cache : HttpRequest.Cache)
    (current : raw) (state : Env Γ) (locals : component.LocalState)
    (invocation : component.ValidInvocation cache current state locals) : ComponentUpdate Γ raw component.LocalState :=
  match component, locals, invocation with
  | .field path .., locals, value => ⟨path.set value current, state, locals⟩
  | .groupOf _ children, locals, invocation => children.applyValid cache current state locals invocation
  | .computed .., _locals, invocation => nomatch invocation
  | .button _ action, locals, _invocation => ⟨current, action.run current state, locals⟩
  | .withAvailability _ body, locals, invocation => body.applyValid cache current state locals invocation.val
  | .choiceOf path _ branches, locals, invocation =>
    (branches.applyValid cache (path.get current) state locals invocation).mapValue (fun value => path.set value current)
  | .list path _ _ initial body, locals, invocation =>
    let items := path.get current
    let rows := items.mapIdx fun index _ => locals[index]?.getD body.initialState
    let Valid index := body.ValidInvocation cache (items.get index) state (locals[index.val]?.getD body.initialState)
    match (invocation : ValidListInvocation items.length Valid) with
    | .add => ⟨path.set (items ++ [initial]) current, state, rows ++ [body.initialState]⟩
    | .remove index => ⟨path.set (items.eraseIdx index) current, state, rows.eraseIdx index⟩
    | .edit index invocation =>
      ((body.applyValid cache (items.get index) state (locals[index.val]?.getD body.initialState) invocation).mapValue
        (fun value => path.set (items.set index value) current)).mapLocals (rows.set index ·)
  | .table path _ _ initial columns selection, locals, invocation =>
    let items := path.get current
    let rows := items.mapIdx fun index _ => locals[index]?.getD columns.initialState
    let Valid index := columns.ValidInvocation cache (items.get index) state (locals[index.val]?.getD columns.initialState)
    match (invocation : ValidTableInvocation items.length Valid selection.isSome) with
    | .add => ⟨path.set (items ++ [initial]) current, state, rows ++ [columns.initialState]⟩
    | .remove index =>
      let next := path.set (items.eraseIdx index) current
      let state := match selection with
        | none => state
        | some selected => selected.set ((selected.get state).remove index.val) state
      ⟨next, state, rows.eraseIdx index⟩
    | .edit index invocation =>
      ((columns.applyValid cache (items.get index) state (locals[index.val]?.getD columns.initialState) invocation).mapValue
        (fun value => path.set (items.set index value) current)).mapLocals (rows.set index ·)
    | .select enabled index =>
      match selection with
      | none => nomatch enabled
      | some selected => ⟨current, selected.set (.row index.val) state, rows⟩
  | .focus target body, locals, invocation =>
    (body.applyValid cache invocation.value state locals invocation.invocation).mapValue fun value =>
      (target.eval current state).set value current
  | .bind _ body, locals, invocation =>
    let updated := body.applyValid cache current (Env.cons locals.value state) locals.tail invocation
    ⟨updated.value, updated.state.tail, ⟨updated.state.value, updated.locals⟩⟩
  | @Component.load _ _ _ _inst source body, locals, invocation =>
    let status := (source.eval current state).resolve cache
    ((body status).applyValid cache current state (locals.at status (body status).initialState) invocation).mapLocals
      (fun updated => ⟨status, updated⟩)

def Components.applyValid {Γ : Context} {raw : Type} (children : Components Γ raw) (cache : HttpRequest.Cache)
    (current : raw) (state : Env Γ) (locals : children.LocalState)
    (invocation : children.ValidInvocation cache current state locals) : ComponentUpdate Γ raw children.LocalState :=
  match children, locals, invocation with
  | .nil, _locals, invocation => nomatch invocation
  | .cons head tail, locals, invocation =>
    match (invocation : head.ValidInvocation cache current state locals.value ⊕ tail.ValidInvocation cache current state locals.tail) with
    | .inl invocation => (head.applyValid cache current state locals.value invocation).mapLocals (⟨·, locals.tail⟩)
    | .inr invocation => (tail.applyValid cache current state locals.tail invocation).mapLocals (⟨locals.value, ·⟩)

def Columns.applyValid {Γ : Context} {raw : Type} (columns : Columns Γ raw) (cache : HttpRequest.Cache)
    (current : raw) (state : Env Γ) (locals : columns.LocalState)
    (invocation : columns.ValidInvocation cache current state locals) : ComponentUpdate Γ raw columns.LocalState :=
  match columns, locals, invocation with
  | .nil, _locals, invocation => nomatch invocation
  | .cons _ head tail, locals, invocation =>
    match (invocation : head.ValidInvocation cache current state locals.value ⊕ tail.ValidInvocation cache current state locals.tail) with
    | .inl invocation => (head.applyValid cache current state locals.value invocation).mapLocals (⟨·, locals.tail⟩)
    | .inr invocation => (tail.applyValid cache current state locals.tail invocation).mapLocals (⟨locals.value, ·⟩)

/-- Re-selecting the active branch keeps its payload. -/
def Branch.applyValid {Γ : Context} {sum : Type} (branch : Branch Γ sum) (cache : HttpRequest.Cache)
    (current : sum) (state : Env Γ) (locals : branch.LocalState)
    (invocation : branch.ValidInvocation cache current state locals) : ComponentUpdate Γ sum branch.LocalState :=
  match branch, locals, invocation with
  | .mk _ _ inject project initial body, locals, invocation =>
    let Valid payload := body.ValidInvocation cache payload state locals
    match (invocation : ValidBranchInvocation (project current) Valid) with
    | .select => ⟨if (project current).isSome then current else inject initial, state, locals⟩
    | .edit payload _ invocation => (body.applyValid cache payload state locals invocation).mapValue inject

def Branches.applyValid {Γ : Context} {sum : Type} (branches : Branches Γ sum) (cache : HttpRequest.Cache)
    (current : sum) (state : Env Γ) (locals : branches.LocalState)
    (invocation : branches.ValidInvocation cache current state locals) : ComponentUpdate Γ sum branches.LocalState :=
  match branches, locals, invocation with
  | .nil, _locals, invocation => nomatch invocation
  | .cons head tail, locals, invocation =>
    match (invocation : head.ValidInvocation cache current state locals.value ⊕ tail.ValidInvocation cache current state locals.tail) with
    | .inl invocation => (head.applyValid cache current state locals.value invocation).mapLocals (⟨·, locals.tail⟩)
    | .inr invocation => (tail.applyValid cache current state locals.tail invocation).mapLocals (⟨locals.value, ·⟩)
end

end Forms.Model
