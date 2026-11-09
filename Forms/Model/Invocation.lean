module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model

inductive ListInvocation (item : Type) where
  | add
  | remove (index : Nat)
  | edit (index : Nat) (invocation : item)

inductive ValidListInvocation (length : Nat) (valid : Fin length → Type) where
  | add
  | remove (index : Fin length)
  | edit (index : Fin length) (invocation : valid index)

inductive BranchInvocation (payload : Type) where
  | select
  | edit (invocation : payload)

/-- A `BranchInvocation` checked against `current`, the active payload if this branch is active. -/
inductive ValidBranchInvocation
    {payload : Type}
    (current : Option payload)
    (valid : payload → Type)
    : Type where
  | select
  | edit (payload : payload) (active : current = some payload) (invocation : valid payload)

inductive InvocationError where
  | hidden
  | disabled
  | inactiveBranch
  | indexOutOfBounds (index length : Nat)
  deriving DecidableEq, Repr

instance : ToString InvocationError where
  toString
    | .hidden => "This action is unavailable: the control is hidden."
    | .disabled => "This action is unavailable: the control is disabled."
    | .inactiveBranch => "This action is unavailable: the option is not selected."
    | .indexOutOfBounds index length =>
      s!"This action is unavailable: item {index + 1} of {length}."

mutual
def Component.Invocation {raw : Type} : Component raw → Type
  | @Component.field _ value .. => value
  | .groupOf _ children => children.Invocation
  | .computed .. => Empty
  | .visibleWhen _ body => body.Invocation
  | .disabledWhen _ body => body.Invocation
  | .choiceOf _ _ branches => branches.Invocation
  | .list _ _ _ _ body => ListInvocation body.Invocation

def Components.Invocation {raw : Type} : Components raw → Type
  | .nil => Empty
  | .cons head tail => head.Invocation ⊕ tail.Invocation

def Branch.Invocation {sum : Type} : Branch sum → Type
  | .mk _ _ _ _ _ body => BranchInvocation body.Invocation

def Branches.Invocation {sum : Type} : Branches sum → Type
  | .nil => Empty
  | .cons head tail => head.Invocation ⊕ tail.Invocation
end

mutual
/-- Invocations that apply to `current`: visible, enabled, in bounds and on the active branch. -/
def Component.ValidInvocation {raw : Type} : Component raw → raw → Type
  | @Component.field _ value .., _ => value
  | .groupOf _ children, current => children.ValidInvocation current
  | .computed .., _ => Empty
  | .visibleWhen condition body, current =>
    { _invocation : body.ValidInvocation current // condition.eval current = true }
  | .disabledWhen condition body, current =>
    { _invocation : body.ValidInvocation current // condition.eval current = false }
  | .choiceOf path _ branches, current => branches.ValidInvocation (path.get current)
  | .list path _ _ _ body, current =>
    ValidListInvocation (path.get current).length fun index =>
      body.ValidInvocation ((path.get current).get index)

def Components.ValidInvocation {raw : Type} : Components raw → raw → Type
  | .nil, _ => Empty
  | .cons head tail, current => head.ValidInvocation current ⊕ tail.ValidInvocation current

def Branch.ValidInvocation {sum : Type} : Branch sum → sum → Type
  | .mk _ _ _ project _ body, current =>
    ValidBranchInvocation (project current) fun payload => body.ValidInvocation payload

def Branches.ValidInvocation {sum : Type} : Branches sum → sum → Type
  | .nil, _ => Empty
  | .cons head tail, current => head.ValidInvocation current ⊕ tail.ValidInvocation current
end

def checkedIndex (index length : Nat) : Except InvocationError (Fin length) :=
  if h : index < length then
    .ok ⟨index, h⟩
  else
    .error (.indexOutOfBounds index length)

mutual
def Component.validate
  {raw : Type}
  (component : Component raw)
  (current : raw)
  (invocation : component.Invocation)
  : Except InvocationError (component.ValidInvocation current) :=
  match component, invocation with
  | .field .., value => .ok value
  | .groupOf _ children, invocation => children.validate current invocation
  | .computed .., invocation => nomatch invocation
  | .visibleWhen condition body, invocation =>
    if h : condition.eval current = true then
      return ⟨← body.validate current invocation, h⟩
    else
      throw .hidden
  | .disabledWhen condition body, invocation =>
    if h : condition.eval current = false then
      return ⟨← body.validate current invocation, h⟩
    else
      throw .disabled
  | .choiceOf path _ branches, invocation => branches.validate (path.get current) invocation
  | .list path _ _ _ body, invocation =>
    let items := path.get current
    match (invocation : ListInvocation body.Invocation) with
    | .add => .ok ValidListInvocation.add
    | .remove index => return ValidListInvocation.remove (← checkedIndex index items.length)
    | .edit index invocation => do
      let index ← checkedIndex index items.length
      return ValidListInvocation.edit index (← body.validate (items.get index) invocation)

def Components.validate
  {raw : Type}
  (children : Components raw)
  (current : raw)
  (invocation : children.Invocation)
  : Except InvocationError (children.ValidInvocation current) :=
  match children, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.Invocation ⊕ tail.Invocation) with
    | .inl invocation => Sum.inl <$> head.validate current invocation
    | .inr invocation => Sum.inr <$> tail.validate current invocation

def Branch.validate
  {sum : Type}
  (branch : Branch sum)
  (current : sum)
  (invocation : branch.Invocation)
  : Except InvocationError (branch.ValidInvocation current) :=
  match branch, invocation with
  | .mk _ _ _ project _ body, invocation =>
    match (invocation : BranchInvocation body.Invocation) with
    | .select => .ok ValidBranchInvocation.select
    | .edit invocation =>
      match active : project current with
      | some payload =>
        ValidBranchInvocation.edit payload active <$> body.validate payload invocation
      | none => throw .inactiveBranch

def Branches.validate
  {sum : Type}
  (branches : Branches sum)
  (current : sum)
  (invocation : branches.Invocation)
  : Except InvocationError (branches.ValidInvocation current) :=
  match branches, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.Invocation ⊕ tail.Invocation) with
    | .inl invocation => Sum.inl <$> head.validate current invocation
    | .inr invocation => Sum.inr <$> tail.validate current invocation
end

mutual
def Component.applyValid
  {raw : Type}
  (component : Component raw)
  (current : raw)
  (invocation : component.ValidInvocation current)
  : raw :=
  match component, invocation with
  | .field path .., value => path.set value current
  | .groupOf _ children, invocation => children.applyValid current invocation
  | .computed .., invocation => nomatch invocation
  | .visibleWhen _ body, invocation => body.applyValid current invocation.val
  | .disabledWhen _ body, invocation => body.applyValid current invocation.val
  | .choiceOf path _ branches, invocation =>
    path.set (branches.applyValid (path.get current) invocation) current
  | .list path _ _ initial body, invocation =>
    let items := path.get current
    let Valid index := body.ValidInvocation (items.get index)
    match (invocation : ValidListInvocation items.length Valid) with
    | .add => path.set (items ++ [initial]) current
    | .remove index => path.set (items.eraseIdx index) current
    | .edit index invocation =>
      path.set (items.set index (body.applyValid (items.get index) invocation)) current

def Components.applyValid
  {raw : Type}
  (children : Components raw)
  (current : raw)
  (invocation : children.ValidInvocation current)
  : raw :=
  match children, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.ValidInvocation current ⊕ tail.ValidInvocation current) with
    | .inl invocation => head.applyValid current invocation
    | .inr invocation => tail.applyValid current invocation

/-- Re-selecting the active branch keeps its payload. -/
def Branch.applyValid
  {sum : Type}
  (branch : Branch sum)
  (current : sum)
  (invocation : branch.ValidInvocation current)
  : sum :=
  match branch, invocation with
  | .mk _ _ inject project initial body, invocation =>
    let Valid payload := body.ValidInvocation payload
    match (invocation : ValidBranchInvocation (project current) Valid) with
    | .select => if (project current).isSome then current else inject initial
    | .edit payload _ invocation => inject (body.applyValid payload invocation)

def Branches.applyValid
  {sum : Type}
  (branches : Branches sum)
  (current : sum)
  (invocation : branches.ValidInvocation current)
  : sum :=
  match branches, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.ValidInvocation current ⊕ tail.ValidInvocation current) with
    | .inl invocation => head.applyValid current invocation
    | .inr invocation => tail.applyValid current invocation
end

def Component.apply
  {raw : Type}
  (component : Component raw)
  (current : raw)
  (invocation : component.Invocation)
  : Except InvocationError raw := do
  return component.applyValid current (← component.validate current invocation)

end Forms.Model
