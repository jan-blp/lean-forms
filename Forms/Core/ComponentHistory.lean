import Forms.Core.Composition
import Forms.Core.ActionInvocation

namespace Forms.Composition

/-- Temporary until all components support replay. -/
def Component.supportsHistory {ty : DataType} : Component ty → Bool
  | .actionWidget .. => true
  | .stack (items := items) _ children _ =>
      (FinEnum.toList items).all fun child => (children child).supportsHistory
  | .computed .. => true
  | .text .. => true
  | .table .. => true
  | .field .. => true
  | .list _ _ item _ => item.supportsHistory
  | .sum .. => false
  | .visibleWhen _ body => body.supportsHistory
  | .disabledWhen _ body => body.supportsHistory
  | .button .. => true

def Component.Invocation {ty : DataType} : Component ty → Type
  | .actionWidget _ _ actions => Action.Invocation (fun name => (actions name).presentation)
  | .stack (items := items) _ children _ => (child : items) × (children child).Invocation
  | .field _ _ widget => Action.Invocation (fun
      | Action.Field.replace => .replace widget)
  | .list _ _ item _ => Action.List item.Invocation
  | .sum .. => Empty
  | .computed .. => Empty
  | .text .. => Empty
  | .table .. => Empty
  | .visibleWhen _ body => body.Invocation
  | .disabledWhen _ body => body.Invocation
  | .button .. => Action.Button

inductive Component.InvocationError where
  | hidden
  | disabled
  | indexOutOfBounds (index length : Nat)
  deriving DecidableEq, BEq, Repr

instance : ToString Component.InvocationError where
  toString
    | .hidden => "Action target is hidden"
    | .disabled => "Action target is disabled"
    | .indexOutOfBounds index length => s!"Index {index} is out of bounds for list of length {length}"

private def checkedIndex
  (index length : Nat)
  : Except Component.InvocationError (Fin length) :=
  if h : index < length then .ok ⟨index, h⟩ else .error (.indexOutOfBounds index length)

def Component.applyInvocation {ty : DataType}
  (component : Component ty)
  (value : ⟦ty⟧)
  : component.Invocation → Except Component.InvocationError ⟦ty⟧ :=
  match component with
  | .actionWidget path _ _ => fun invocation =>
      .ok (path.set (invocation.apply (path.get value)) value)
  | .stack _ children _ => fun ⟨child, invocation⟩ =>
      (children child).applyInvocation value invocation
  | .field path _ _ => fun invocation =>
      .ok (path.set (invocation.apply (path.get value)) value)
  | .list path _ item defaultItem => fun invocation => do
      let items := path.get value
      match invocation with
      | .appendDefault => return path.set (items ++ [defaultItem]) value
      | .remove index =>
          let index ← checkedIndex index items.length
          return path.set (items.eraseIdx index.val) value
      | .item index invocation =>
          let index ← checkedIndex index items.length
          let updated ← item.applyInvocation (items.get index) invocation
          return path.set (items.set index.val updated) value
  | .sum .. => fun invocation => Empty.elim invocation
  | .computed .. => fun invocation => Empty.elim invocation
  | .text .. => fun invocation => Empty.elim invocation
  | .table .. => fun invocation => Empty.elim invocation
  | .visibleWhen condition body => fun invocation =>
      if condition.eval value then body.applyInvocation value invocation else .error .hidden
  | .disabledWhen condition body => fun invocation =>
      if condition.eval value then .error .disabled else body.applyInvocation value invocation
  | .button _ action => fun
      | .press => .ok (action.eval value)

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
