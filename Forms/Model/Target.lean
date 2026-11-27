module

public import Forms.Model.Invocation

@[expose] public section
namespace Forms.Model

inductive Target (Γ : Context) (α β : Type) where
  /-- stored in the model -/
  | path (path : Path α β)
  /-- stored only in private state -/
  | var (var : Var Γ β)

def Target.get
  {Γ : Context}
  {α β : Type}
  (target : Target Γ α β)
  (value : α)
  (env : Env Γ)
  : β :=
  match target with
  | .path focus => focus.get value
  | .var ref => ref.get env

def Target.set
  {Γ : Context}
  {α β : Type}
  (target : Target Γ α β)
  (new : β)
  (value : α)
  (env : Env Γ)
  : ComponentUpdate Γ α Unit :=
  match target with
  | .path focus =>
    { value := focus.set new value, state := env, locals := (), invalidations := [], call := none }
  | .var ref => { value, state := ref.set new env, locals := (), invalidations := [], call := none }

def Target.rename
  {Γ Δ : Context}
  {α β : Type}
  (rename : Renaming Γ Δ)
  : Target Γ α β → Target Δ α β
  | .path focus => .path focus
  | .var ref => .var (rename ref)

end Forms.Model
