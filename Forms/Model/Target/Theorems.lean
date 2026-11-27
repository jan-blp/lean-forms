module

public import Forms.Model.Target
public import Forms.Model.Path.Theorems
public import Forms.Model.Context.Theorems

public section
namespace Forms.Model

theorem Target.get_set
  {Γ : Context}
  {α β : Type}
  (target : Target Γ α β)
  (new : β)
  (value : α)
  (env : Env Γ)
  : let updated := target.set new value env
    target.get updated.value updated.state = new := by
  cases target with
  | path focus => exact Path.get_set focus new value
  | var ref => exact Var.get_set ref new env

theorem Target.set_var_value
  {Γ : Context}
  {α β : Type}
  (ref : Var Γ β)
  (new : β)
  (value : α)
  (env : Env Γ)
  : ((Target.var ref).set new value env).value = value :=
  rfl

theorem Target.set_path_state
  {Γ : Context}
  {α β : Type}
  (focus : Path α β)
  (new : β)
  (value : α)
  (env : Env Γ)
  : ((Target.path focus).set new value env).state = env :=
  rfl

end Forms.Model
