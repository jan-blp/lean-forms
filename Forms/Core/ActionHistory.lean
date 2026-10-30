import Forms.Core.WidgetAction

namespace Forms

inductive ActionInvocation (ty : DataType) (action : Type) where
  | button (name : action)
  | editor (name : action) (argument : ⟦ty⟧)

/-- Current value and ordered invocations. -/
structure ActionHistory (ty : DataType) (action : Type) where
  value : ⟦ty⟧
  actions : Array (ActionInvocation ty action) := #[]

namespace ActionHistory

/-- Apply and record an invocation from trusted definitions. -/
def apply {ty : DataType} {action : Type} (definitions : action → ActionPresentation ty)
    (history : ActionHistory ty action) (invocation : ActionInvocation ty action)
    : Except String (ActionHistory ty action) := do
  let value ← match invocation with
    | .button name => match definitions name with
      | .button body => pure (body.eval history.value)
      | .editor .. => throw "Action requires an editor argument"
    | .editor name argument => match definitions name with
      | .button .. => throw "Button does not accept an argument"
      | .editor _ body => pure (body.eval (fun
          | .current => history.value
          | .argument => argument))
  return ⟨value, history.actions.push invocation⟩

def replay {ty : DataType} {action : Type} (definitions : action → ActionPresentation ty)
    (initial : ⟦ty⟧) (actions : Array (ActionInvocation ty action))
    : Except String (ActionHistory ty action) :=
  actions.foldlM (apply definitions) ⟨initial, #[]⟩

end ActionHistory
end Forms
