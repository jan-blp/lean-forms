module

public import Forms.Model.Computation
public import Forms.Model.Invocation
public import Forms.Model.FreshId

@[expose] public section
namespace Forms.Model

inductive Action.Step (Γ : Context) (α : Type) where
  | set {β : Type}
      (ref : Var Γ β)
      (value : Computation Γ α β)
      : Action.Step Γ α
  | append {β : Type}
      (path : Path α (Collection β))
      (item : Computation Γ α β)
      : Action.Step Γ α
  | write {β : Type}
      (path : Path α β)
      (value : Computation Γ α β)
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

/-- Adds `item` to the collection at `path`, with a fresh id. -/
def append
  {Γ : Context}
  {α β : Type}
  (path : Path α (Collection β))
  (item : Computation Γ α β)
  : Action Γ α :=
  FreeMonoid.of (.append path item)

def write
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  (value : Computation Γ α β)
  : Action Γ α :=
  FreeMonoid.of (.write path value)

def Step.rename
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  : Step Γ α → Step Δ α
  | .set ref value => .set (rename ref) (value.rename rename)
  | .append path item => .append path (item.rename rename)
  | .write path value => .write path (value.rename rename)
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
  {m : Type → Type}
  [Monad m]
  [MonadFreshId m]
  (step : Step Γ α)
  (value : α)
  (env : Env Γ)
  : ExceptT Collection.IdCollision m (ComponentUpdate Γ α Unit) :=
  match step with
  | .set ref computed =>
    pure { value, state := ref.set (computed.eval value env) env, locals := () }
  | .append path item => do
    let updated ← (path.get value).appendFresh (item.eval value env)
    return { value := path.set updated value, state := env, locals := () }
  | .write path computed =>
    pure { value := path.set (computed.eval value env) value, state := env, locals := () }
  | .visit target =>
    pure { value, state := env, locals := (), visit := target.eval value env }

def run
  {Γ : Context}
  {α : Type}
  {m : Type → Type}
  [Monad m]
  [MonadFreshId m]
  (action : Action Γ α)
  (value : α)
  (env : Env Γ)
  : ExceptT Collection.IdCollision m (ComponentUpdate Γ α Unit) :=
  action.toList.foldlM (fun updated step => do
    let next ← step.run updated.value updated.state
    return { next with visit := next.visit.orElse fun _ => updated.visit })
    { value, state := env, locals := () }

/-- Focuses `target` after the action runs. -/
def visit
  {Γ : Context}
  {α : Type}
  (target : Computation Γ α (Option Destination))
  : Action Γ α :=
  FreeMonoid.of (.visit target)

end Action

end Forms.Model
