import Forms.Core.Widget

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

/-- Editors supply an argument of the same type as the current widget value. -/
abbrev ActionContext (ty : DataType) : DataType := .record actionInputs fun _ => ty

inductive ActionPresentation (ty : DataType) where
  | button (body : Expr ty ty)
  | editor (widget : Widget ty) (body : Expr (ActionContext ty) ty)

structure WidgetAction (ty : DataType) where
  label : String
  presentation : ActionPresentation ty

def WidgetAction.eval {ty : DataType} (action : WidgetAction ty)
    (inputs : ⟦ActionContext ty⟧) : ⟦ty⟧ :=
  match action.presentation with
  | .button body => body.eval (inputs .current)
  | .editor _ body => body.eval inputs

end Forms
