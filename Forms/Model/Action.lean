module

public import Forms.Model.Computation
public import Forms.Model.Invocation

@[expose] public section
namespace Forms.Model

inductive Action.Step (Γ : Context) (α : Type) where
  | set {β : Type}
      (ref : Var Γ β)
      (value : Computation Γ α β)
      : Action.Step Γ α
  | append {β : Type}
      (path : Path α (List β))
      (item : Computation Γ α β)
      : Action.Step Γ α

abbrev Action (Γ : Context) (α : Type) := FreeMonoid (Action.Step Γ α)

namespace Action

instance {Γ : Context} {α : Type} : Append (Action Γ α) where
  append := (· * ·)

def set
  {Γ : Context}
  {α β : Type}
  (ref : Var Γ β)
  (value : Computation Γ α β)
  : Action Γ α :=
  FreeMonoid.of (.set ref value)

def append
  {Γ : Context}
  {α β : Type}
  (path : Path α (List β))
  (item : Computation Γ α β)
  : Action Γ α :=
  FreeMonoid.of (.append path item)

def Step.rename
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  : Step Γ α → Step Δ α
  | .set ref value => .set (rename ref) (value.rename rename)
  | .append path item => .append path (item.rename rename)

def rename
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  (action : Action Γ α)
  : Action Δ α :=
  FreeMonoid.map (·.rename rename) action

def Step.run
  {Γ : Context}
  {α : Type}
  (step : Step Γ α)
  (value : α)
  (env : Env Γ)
  : ComponentUpdate Γ α Unit :=
  match step with
  | .set ref computed => ⟨value, ref.set (computed.eval value env) env, ()⟩
  | .append path item => ⟨path.set (path.get value ++ [item.eval value env]) value, env, ()⟩

def run
  {Γ : Context}
  {α : Type}
  (action : Action Γ α)
  (value : α)
  (env : Env Γ)
  : ComponentUpdate Γ α Unit :=
  action.toList.foldl (fun updated step => step.run updated.value updated.state) ⟨value, env, ()⟩

end Action

end Forms.Model
