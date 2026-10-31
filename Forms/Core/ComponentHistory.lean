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

def Component.ValidInvocation {ty : DataType}
  (component : Component ty)
  (current : ⟦ty⟧)
  : Type :=
  match component with
  | .actionWidget _ _ actions => Action.Invocation (fun name => (actions name).presentation)
  | .field _ _ widget => Action.Invocation (fun
      | Action.Field.replace => .replace widget)
  | .button .. => Action.Button
  | .stack (items := items) _ children _ =>
      (child : items) × (children child).ValidInvocation current
  | .list path _ item _ =>
      Action.List.ValidInvocation (path.get current).length fun index =>
        item.ValidInvocation ((path.get current).get index)
  | .visibleWhen condition body =>
      { _invocation : body.ValidInvocation current // condition.eval current = true }
  | .disabledWhen condition body =>
      { _invocation : body.ValidInvocation current // condition.eval current = false }
  | .sum .. => Empty
  | .computed .. => Empty
  | .text .. => Empty
  | .table .. => Empty

private def checkedIndex
  (index length : Nat)
  : Except Component.InvocationError (Fin length) :=
  if h : index < length then .ok ⟨index, h⟩ else .error (.indexOutOfBounds index length)

def Component.validateInvocation {ty : DataType}
  (component : Component ty)
  (current : ⟦ty⟧)
  (invocation : component.Invocation)
  : Except Component.InvocationError (component.ValidInvocation current) :=
  match component with
  | .actionWidget .. => .ok invocation
  | .field .. => .ok invocation
  | .button .. => .ok invocation
  | .stack _ children _ => do
      let validated ← (children invocation.1).validateInvocation current invocation.2
      return ⟨invocation.1, validated⟩
  | .list path _ item _ =>
      match invocation with
      | .appendDefault => .ok .appendDefault
      | .remove index => do
          return .remove (← checkedIndex index (path.get current).length)
      | .item index invocation => do
          let index ← checkedIndex index (path.get current).length
          let validated ← item.validateInvocation ((path.get current).get index) invocation
          return .item index validated
  | .visibleWhen condition body => do
      if h : condition.eval current = true then
        let validated ← body.validateInvocation current invocation
        return ⟨validated, h⟩
      else .error .hidden
  | .disabledWhen condition body => do
      if h : condition.eval current = false then
        let validated ← body.validateInvocation current invocation
        return ⟨validated, h⟩
      else .error .disabled
  | .sum .. => Empty.elim invocation
  | .computed .. => Empty.elim invocation
  | .text .. => Empty.elim invocation
  | .table .. => Empty.elim invocation

def Component.applyValidInvocation {ty : DataType}
  (component : Component ty)
  (current : ⟦ty⟧)
  (invocation : component.ValidInvocation current)
  : ⟦ty⟧ :=
  match component with
  | .actionWidget path _ _ =>
      path.set (invocation.apply (path.get current)) current
  | .field path _ _ =>
      path.set (invocation.apply (path.get current)) current
  | .stack _ children _ =>
      (children invocation.1).applyValidInvocation current invocation.2
  | .list path _ item defaultItem =>
      match invocation with
      | .appendDefault => path.set (path.get current ++ [defaultItem]) current
      | .remove index => path.set ((path.get current).eraseIdx index.val) current
      | .item index invocation =>
          let updated := item.applyValidInvocation ((path.get current).get index) invocation
          path.set ((path.get current).set index.val updated) current
  | .visibleWhen _ body => body.applyValidInvocation current invocation.val
  | .disabledWhen _ body => body.applyValidInvocation current invocation.val
  | .button _ action =>
      match invocation with
      | .press => action.eval current
  | .sum .. => Empty.elim invocation
  | .computed .. => Empty.elim invocation
  | .text .. => Empty.elim invocation
  | .table .. => Empty.elim invocation

def Component.applyInvocation {ty : DataType}
  (component : Component ty)
  (current : ⟦ty⟧)
  (invocation : component.Invocation)
  : Except Component.InvocationError ⟦ty⟧ := do
  let validated ← component.validateInvocation current invocation
  return component.applyValidInvocation current validated

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
