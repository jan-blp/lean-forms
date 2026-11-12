module

public import Forms.Model.Computation

@[expose] public section
namespace Forms.Model

/-- An update to UI state, evaluated against the model and context when invoked. -/
inductive Action (Γ : Context) (α : Type) where
  | set {β : Type}
      (ref : Var Γ β)
      (value : Computation Γ α β)
      : Action Γ α

/-- Runs an action without changing the model. -/
def Action.run
  {Γ : Context}
  {α : Type}
  (action : Action Γ α)
  (sourceValue : α)
  (env : Env Γ)
  : Env Γ :=
  match action with
  | .set ref value => ref.set (value.eval sourceValue env) env

end Forms.Model
