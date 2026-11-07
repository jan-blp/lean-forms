module

public import Forms.Core.Widget

@[expose] public section

namespace Forms

inductive ActionInput where
  | current
  | argument
  deriving DecidableEq

instance : FinEnum ActionInput :=
  FinEnum.ofList [.current, .argument] (by grind [ActionInput])

def actionInputs : Enum where
  type := ActionInput
  label
    | .current => "current"
    | .argument => "argument"

abbrev ActionContext (ty : DataType) : DataType := .record actionInputs fun _ => ty

inductive Action.Presentation (ty : DataType) where
  | button (body : ⟦ty⟧ → ⟦ty⟧)
  | editor (widget : Widget ty) (body : ⟦ActionContext ty⟧ → ⟦ty⟧)

inductive Action.Field where
  | replace

def Action.Presentation.replace {ty : DataType}
  (widget : Widget ty)
  : Action.Presentation ty :=
  .editor widget (fun inputs => inputs .argument)

structure WidgetAction (ty : DataType) where
  label : String
  presentation : Action.Presentation ty

def WidgetAction.eval {ty : DataType}
  (action : WidgetAction ty)
  (inputs : ⟦ActionContext ty⟧)
  : ⟦ty⟧ :=
  match action.presentation with
  | .button body => body (inputs .current)
  | .editor _ body => body inputs

end Forms
