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
  | invalidate (scope : Computation Γ α RequestScope)
      : Action.Step Γ α
  /-- Sends `request` once; `andThen` and the steps after it run when the result arrives. -/
  | call {β : Type}
      (request : Computation Γ α HttpRequest)
      (decode : Lean.Json → Except String β)
      (andThen : Except String β → FreeMonoid (Action.Step Γ α))
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

mutual
def Step.rename
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  : Step Γ α → Step Δ α
  | .set ref value => .set (rename ref) (value.rename rename)
  | .append path item => .append path (item.rename rename)
  | .write path value => .write path (value.rename rename)
  | .visit target => .visit (target.rename rename)
  | .invalidate scope => .invalidate (scope.rename rename)
  | .call request decode andThen =>
    .call (request.rename rename) decode fun result => Action.rename rename (andThen result)

def rename
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  : Action Γ α → Action Δ α
  | ⟨steps⟩ => ⟨Step.renameAll rename steps⟩

def Step.renameAll
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  : List (Step Γ α) → List (Step Δ α)
  | [] => []
  | step :: steps => step.rename rename :: Step.renameAll rename steps
end

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
    pure {
      value, state := ref.set (computed.eval value env) env
      locals := (), invalidations := [], call := none }
  | .append path item => do
    let updated ← (path.get value).appendFresh (item.eval value env)
    return {
      value := path.set updated value, state := env
      locals := (), invalidations := [], call := none }
  | .write path computed =>
    pure {
      value := path.set (computed.eval value env) value
      state := env, locals := (), invalidations := [], call := none }
  | .visit target =>
    pure {
      value, state := env, locals := (), invalidations := [], call := none
      visit := target.eval value env }
  | .invalidate scope =>
    pure {
      value, state := env, locals := ()
      invalidations := [scope.eval value env], call := none }
  | .call request .. => do
    let id ← (freshId : m Uuid)
    return {
      value, state := env, locals := (), invalidations := []
      call := some { id, request := request.eval value env } }

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
  go action.toList { value, state := env, locals := (), invalidations := [], call := none }
where
  go : List (Step Γ α) → ComponentUpdate Γ α Unit →
      ExceptT Collection.IdCollision m (ComponentUpdate Γ α Unit)
    | [], updated => pure updated
    | step :: steps, updated => do
      let next ← step.run updated.value updated.state
      let next := { next with
        visit := next.visit.orElse fun _ => updated.visit
        invalidations := updated.invalidations ++ next.invalidations }
      match next.call with
      | some _ => pure next
      | none => go steps next

def afterCall
  {Γ : Context}
  {α : Type}
  (result : Except String Lean.Json)
  : List (Step Γ α) → Option (Action Γ α)
  | [] => none
  | .call _ decode andThen :: steps => some (andThen (result >>= decode) * ⟨steps⟩)
  | .set .. :: steps
  | .append .. :: steps
  | .write .. :: steps
  | .visit _ :: steps
  | .invalidate _ :: steps => afterCall result steps

def resume
  {Γ : Context}
  {α : Type}
  (action : Action Γ α)
  : List (Except String Lean.Json) → Option (Action Γ α)
  | [] => some action
  | result :: results => do (← afterCall result action.toList).resume results

def call
  {Γ : Context}
  {α : Type}
  {endpoint : Type}
  [FinEnum endpoint]
  [Api endpoint]
  (named : endpoint)
  (input : Computation Γ α (Api.signature named).Input)
  (andThen : Except String (Api.signature named).Output → Action Γ α)
  : Action Γ α :=
  FreeMonoid.of (.call (Api.request named <$> input) Lean.fromJson? andThen)

/-- Focuses `target` after the action runs. -/
def visit
  {Γ : Context}
  {α : Type}
  (target : Computation Γ α (Option Destination))
  : Action Γ α :=
  FreeMonoid.of (.visit target)

/-- Drops matching cached responses; active sources are fetched again after the action. -/
def invalidate
  {Γ : Context}
  {α : Type}
  (scope : Computation Γ α RequestScope)
  : Action Γ α :=
  FreeMonoid.of (.invalidate scope)

end Action

end Forms.Model
