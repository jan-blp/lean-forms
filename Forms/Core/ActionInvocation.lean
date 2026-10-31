import Forms.Core.WidgetAction

namespace Forms.Action

inductive List (itemInvocation : Type) where
  | appendDefault
  | remove (index : Nat)
  | item (index : Nat) (invocation : itemInvocation)

abbrev Presentation.Argument {ty : DataType} : Presentation ty → Type
  | .button .. => Unit
  | .editor .. => ⟦ty⟧

structure Invocation {ty : DataType} {actionName : Type}
  (definitions : actionName → Presentation ty) where
  name : actionName
  argument : (definitions name).Argument

private def applyArgument {ty : DataType}
  (presentation : Presentation ty)
  (current : ⟦ty⟧)
  : presentation.Argument → ⟦ty⟧ :=
  match presentation with
  | .button body => fun () => body.eval current
  | .editor _ body => fun argument => body.eval (fun
      | .current => current
      | .argument => argument)

def Invocation.apply {ty : DataType} {actionName : Type}
  {definitions : actionName → Presentation ty}
  (current : ⟦ty⟧)
  (invocation : Invocation definitions)
  : ⟦ty⟧ :=
  applyArgument (definitions invocation.name) current invocation.argument

end Forms.Action
