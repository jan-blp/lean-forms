module

public import Forms.Model.Computation
public import Forms.Model.Invocation

@[expose] public section
namespace Forms.Model

/-- An update evaluated against the model and context when invoked. -/
inductive Action (Γ : Context) (α : Type) where
  | set {β : Type}
      (ref : Var Γ β)
      (value : Computation Γ α β)
      : Action Γ α
  /-- Appends `item` to the list at `path`. -/
  | append {β : Type}
      (path : Path α (List β))
      (item : Computation Γ α β)
      : Action Γ α

def Action.rename
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  : Action Γ α → Action Δ α
  | .set ref value => .set (rename ref) (value.rename rename)
  | .append path item => .append path (item.rename rename)

def Action.run
  {Γ : Context}
  {α : Type}
  (action : Action Γ α)
  (value : α)
  (env : Env Γ)
  : ComponentUpdate Γ α Unit :=
  match action with
  | .set ref computed => ⟨value, ref.set (computed.eval value env) env, ()⟩
  | .append path item => ⟨path.set (path.get value ++ [item.eval value env]) value, env, ()⟩

end Forms.Model
