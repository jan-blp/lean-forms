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
  | visit (target : Computation Γ α (Option Destination))
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
  | .visit target => .visit (target.rename rename)

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
  | .set ref computed => { value, state := ref.set (computed.eval value env) env, locals := () }
  | .append path item =>
    { value := path.set (path.get value ++ [item.eval value env]) value
      state := env, locals := (), invalidatesDestinations := true }
  | .visit target => { value, state := env, locals := (), visit := target.eval value env }

def run
  {Γ : Context}
  {α : Type}
  (action : Action Γ α)
  (value : α)
  (env : Env Γ)
  : ComponentUpdate Γ α Unit :=
  action.toList.foldl (fun updated step =>
    let next := step.run updated.value updated.state
    { next with
      visit := next.visit.orElse fun _ => updated.visit
      invalidatesDestinations := updated.invalidatesDestinations || next.invalidatesDestinations })
    { value, state := env, locals := () }

def visit
  {Γ : Context}
  {α : Type}
  (target : Computation Γ α (Option Destination))
  : Action Γ α :=
  FreeMonoid.of (.visit target)

end Action

end Forms.Model
