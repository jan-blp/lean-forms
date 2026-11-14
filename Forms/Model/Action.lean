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

def Action.rename
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  : Action Γ α → Action Δ α
  | .set ref value => .set (rename ref) (value.rename rename)

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
