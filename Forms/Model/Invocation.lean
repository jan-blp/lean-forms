module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model

inductive ValidListInvocation (length : Nat) (valid : Fin length → Type) where
  | add
  | remove (index : Fin length)
  | edit (index : Fin length) (invocation : valid index)

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
/-- Invocations that apply to `current`: visible, enabled, in bounds, on the active branch, in the
subtree each load builds from its current status. -/
def Component.ValidInvocation {raw : Type} : Component raw → HttpRequest.Cache → raw → Type
  | @Component.field _ value .., _, _ => value
  | .groupOf _ children, cache, current => children.ValidInvocation cache current
  | .computed .., _, _ => Empty
  | .visibleWhen condition body, cache, current =>
    { _invocation : body.ValidInvocation cache current // condition.eval current = true }
  | .disabledWhen condition body, cache, current =>
    { _invocation : body.ValidInvocation cache current // condition.eval current = false }
  | .choiceOf path _ branches, cache, current => branches.ValidInvocation cache (path.get current)
  | .list path _ _ _ body, cache, current =>
    ValidListInvocation (path.get current).length fun index =>
      body.ValidInvocation cache ((path.get current).get index)
  | .load source body, cache, current =>
    (body ((source.eval current).resolve cache)).ValidInvocation cache current

def Components.ValidInvocation {raw : Type} : Components raw → HttpRequest.Cache → raw → Type
  | .nil, _, _ => Empty
  | .cons head tail, cache, current =>
    head.ValidInvocation cache current ⊕ tail.ValidInvocation cache current

def Branch.ValidInvocation {sum : Type} : Branch sum → HttpRequest.Cache → sum → Type
  | .mk _ _ _ project _ body, cache, current =>
    ValidBranchInvocation (project current) fun payload => body.ValidInvocation cache payload

def Branches.ValidInvocation {sum : Type} : Branches sum → HttpRequest.Cache → sum → Type
  | .nil, _, _ => Empty
  | .cons head tail, cache, current =>
    head.ValidInvocation cache current ⊕ tail.ValidInvocation cache current
end

def checkedIndex (index length : Nat) : Except InvocationError (Fin length) :=
  if h : index < length then
    .ok ⟨index, h⟩
  else
    .error (.indexOutOfBounds index length)

mutual
def Component.applyValid
  {raw : Type}
  (component : Component raw)
  (cache : HttpRequest.Cache)
  (current : raw)
  (invocation : component.ValidInvocation cache current)
  : raw :=
  match component, invocation with
  | .field path .., value => path.set value current
  | .groupOf _ children, invocation => children.applyValid cache current invocation
  | .computed .., invocation => nomatch invocation
  | .visibleWhen _ body, invocation => body.applyValid cache current invocation.val
  | .disabledWhen _ body, invocation => body.applyValid cache current invocation.val
  | .choiceOf path _ branches, invocation =>
    path.set (branches.applyValid cache (path.get current) invocation) current
  | .list path _ _ initial body, invocation =>
    let items := path.get current
    let Valid index := body.ValidInvocation cache (items.get index)
    match (invocation : ValidListInvocation items.length Valid) with
    | .add => path.set (items ++ [initial]) current
    | .remove index => path.set (items.eraseIdx index) current
    | .edit index invocation =>
      path.set (items.set index (body.applyValid cache (items.get index) invocation)) current
  | .load source body, invocation =>
    (body ((source.eval current).resolve cache)).applyValid cache current invocation

def Components.applyValid
  {raw : Type}
  (children : Components raw)
  (cache : HttpRequest.Cache)
  (current : raw)
  (invocation : children.ValidInvocation cache current)
  : raw :=
  match children, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.ValidInvocation cache current ⊕ tail.ValidInvocation cache current) with
    | .inl invocation => head.applyValid cache current invocation
    | .inr invocation => tail.applyValid cache current invocation

/-- Re-selecting the active branch keeps its payload. -/
def Branch.applyValid
  {sum : Type}
  (branch : Branch sum)
  (cache : HttpRequest.Cache)
  (current : sum)
  (invocation : branch.ValidInvocation cache current)
  : sum :=
  match branch, invocation with
  | .mk _ _ inject project initial body, invocation =>
    let Valid payload := body.ValidInvocation cache payload
    match (invocation : ValidBranchInvocation (project current) Valid) with
    | .select => if (project current).isSome then current else inject initial
    | .edit payload _ invocation => inject (body.applyValid cache payload invocation)

def Branches.applyValid
  {sum : Type}
  (branches : Branches sum)
  (cache : HttpRequest.Cache)
  (current : sum)
  (invocation : branches.ValidInvocation cache current)
  : sum :=
  match branches, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.ValidInvocation cache current ⊕ tail.ValidInvocation cache current) with
    | .inl invocation => head.applyValid cache current invocation
    | .inr invocation => tail.applyValid cache current invocation
end

end Forms.Model
