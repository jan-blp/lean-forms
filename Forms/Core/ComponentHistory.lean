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
  | .visibleWhen .. => false
  | .disabledWhen .. => false
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
  | .visibleWhen .. => Empty
  | .disabledWhen .. => Empty
  | .button .. => Empty
  | .appendItemButton .. => Empty

def Component.applyInvocation {ty : DataType}
  (component : Component ty)
  (value : ⟦ty⟧)
  : component.Invocation → ⟦ty⟧ :=
  match component with
  | .actionWidget path _ _ => fun invocation =>
      path.set (invocation.apply (path.get value)) value
  | .stack _ children _ => fun ⟨child, invocation⟩ =>
      (children child).applyInvocation value invocation
  | .field .. => fun invocation => Empty.elim invocation
  | .list .. => fun invocation => Empty.elim invocation
  | .sum .. => fun invocation => Empty.elim invocation
  | .computed .. => fun invocation => Empty.elim invocation
  | .text .. => fun invocation => Empty.elim invocation
  | .table .. => fun invocation => Empty.elim invocation
  | .visibleWhen .. => fun invocation => Empty.elim invocation
  | .disabledWhen .. => fun invocation => Empty.elim invocation
  | .button .. => fun invocation => Empty.elim invocation
  | .appendItemButton .. => fun invocation => Empty.elim invocation

structure ComponentHistory {ty : DataType} (component : Component ty) where
  value : ⟦ty⟧
  actions : Array component.Invocation := #[]

def ComponentHistory.apply {ty : DataType} {component : Component ty}
  (history : ComponentHistory component)
  (invocation : component.Invocation)
  : ComponentHistory component :=
  { value := component.applyInvocation history.value invocation
    actions := history.actions.push invocation }

def ComponentHistory.replay {ty : DataType}
  (component : Component ty)
  (initial : ⟦ty⟧)
  (actions : Array component.Invocation)
  : ComponentHistory component :=
  actions.foldl ComponentHistory.apply ⟨initial, #[]⟩

end Forms.Composition
