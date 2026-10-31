import Forms.Core.WidgetAction

namespace Forms.Action

inductive Invocation (ty : DataType) (actionName : Type) where
  | button (name : actionName)
  | editor (name : actionName) (argument : ⟦ty⟧)

inductive InvocationError where
  | missingArgument
  | unexpectedArgument
  deriving DecidableEq, BEq, Repr

instance : ToString InvocationError where
  toString
    | .missingArgument => "Action requires an editor argument"
    | .unexpectedArgument => "Button does not accept an argument"

def Invocation.apply {ty : DataType} {actionName : Type}
    (definitions : actionName → Presentation ty)
    (current : ⟦ty⟧)
    (invocation : Invocation ty actionName)
    : Except InvocationError ⟦ty⟧ :=
  match invocation with
  | .button name => match definitions name with
    | .button body => .ok (body.eval current)
    | .editor .. => .error .missingArgument
  | .editor name argument => match definitions name with
    | .button .. => .error .unexpectedArgument
    | .editor _ body => .ok (body.eval (fun
        | .current => current
        | .argument => argument))

end Forms.Action
