import Forms.Core.Composition
import Forms.Core.ActionInvocation

namespace Forms.Composition

def Component.supportsHistory {ty : DataType} : Component ty → Bool
  | .actionWidget .. => true
  | .stack (items := items) _ children _ =>
      (FinEnum.toList items).all fun child => (children child).supportsHistory
  | .computed .. => true
  | .text .. => true
  | .table .. => true
  | .field .. => false
  | .list .. => false
  | .sum .. => false
  | .visibleWhen _ body => body.supportsHistory
  | .disabledWhen _ body => body.supportsHistory
  | .button .. => false
  | .appendItemButton .. => false

/-- Targets use component identities, not display positions or state paths. -/
def Component.Invocation {ty : DataType} : Component ty → Type
  | .actionWidget _ _ actions => Action.Invocation (fun name => (actions name).presentation)
  | .stack (items := items) _ children _ => (child : items) × (children child).Invocation
  | .field .. => Empty
  | .list .. => Empty
  | .sum .. => Empty
  | .computed .. => Empty
  | .text .. => Empty
  | .table .. => Empty
  | .visibleWhen _ body => body.Invocation
  | .disabledWhen _ body => body.Invocation
  | .button .. => Empty
  | .appendItemButton .. => Empty

inductive Component.InvocationError where
  | hidden
  | disabled
  deriving DecidableEq, BEq, Repr

instance : ToString Component.InvocationError where
  toString
    | .hidden => "Action target is hidden"
    | .disabled => "Action target is disabled"

def Component.applyInvocation {ty : DataType}
  (component : Component ty)
  (value : ⟦ty⟧)
  : component.Invocation → Except Component.InvocationError ⟦ty⟧ :=
  match component with
  | .actionWidget path _ _ => fun invocation =>
      .ok (path.set (invocation.apply (path.get value)) value)
  | .stack _ children _ => fun ⟨child, invocation⟩ =>
      (children child).applyInvocation value invocation
  | .field .. => fun invocation => Empty.elim invocation
  | .list .. => fun invocation => Empty.elim invocation
  | .sum .. => fun invocation => Empty.elim invocation
  | .computed .. => fun invocation => Empty.elim invocation
  | .text .. => fun invocation => Empty.elim invocation
  | .table .. => fun invocation => Empty.elim invocation
  | .visibleWhen condition body => fun invocation =>
      if condition.eval value then body.applyInvocation value invocation else .error .hidden
  | .disabledWhen condition body => fun invocation =>
      if condition.eval value then .error .disabled else body.applyInvocation value invocation
  | .button .. => fun invocation => Empty.elim invocation
  | .appendItemButton .. => fun invocation => Empty.elim invocation

structure ComponentHistory {ty : DataType} (component : Component ty) where
  value : ⟦ty⟧
  actions : Array component.Invocation := #[]

def ComponentHistory.apply {ty : DataType} {component : Component ty}
  (history : ComponentHistory component)
  (invocation : component.Invocation)
  : Except Component.InvocationError (ComponentHistory component) := do
  let value ← component.applyInvocation history.value invocation
  return { value, actions := history.actions.push invocation }

def ComponentHistory.replay {ty : DataType}
  (component : Component ty)
  (initial : ⟦ty⟧)
  (actions : Array component.Invocation)
  : Except Component.InvocationError (ComponentHistory component) :=
  actions.foldlM ComponentHistory.apply ⟨initial, #[]⟩

end Forms.Composition
