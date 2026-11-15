module

public import Forms.Model.Computation

public section
namespace Forms.Model

universe u v w

/-- Evaluation depends only on the declared inputs; changes elsewhere do not affect it. -/
theorem Computation.eval_congr
  {Γ : Context}
  {α : Type} {β : Type u}
  (computation : Computation Γ α β)
  (first second : α)
  (firstState secondState : Env Γ)
  (h : computation.inputs.read first firstState = computation.inputs.read second secondState)
  : computation.eval first firstState = computation.eval second secondState :=
  congrArg (Inputs.apply computation.run) h

theorem Inputs.apply_map
  {types : List Type}
  {α : Type u} {β : Type v}
  (f : α → β)
  (fn : Inputs.Function types α)
  (values : Inputs.Values types)
  : Inputs.apply (Inputs.Function.map f fn) values = f (Inputs.apply fn values) := by
  induction types with
  | nil => rfl
  | cons _ _ ih => exact ih (fn values.1) values.2

theorem Inputs.Function.map_id
  {types : List Type}
  {α : Type u}
  (fn : Inputs.Function types α)
  : Inputs.Function.map id fn = fn := by
  induction types with
  | nil =>
    rfl
  | cons _ _ ih =>
    exact funext fun value => ih (fn value)

theorem Inputs.Function.map_comp
  {types : List Type}
  {α : Type u} {β : Type v} {γ : Type w}
  (g : α → β)
  (h : β → γ)
  (fn : Inputs.Function types α)
  : Inputs.Function.map (h ∘ g) fn = Inputs.Function.map h (Inputs.Function.map g fn) := by
  induction types with
  | nil =>
    rfl
  | cons _ _ ih =>
    exact funext fun value => ih (fn value)

instance {Γ : Context} {α : Type} : LawfulFunctor (Computation Γ α) where
  map_const := rfl
  id_map computation := by
    cases computation
    exact congrArg _ (Inputs.Function.map_id _)
  comp_map g h computation := by
    cases computation
    exact congrArg _ (Inputs.Function.map_comp g h _)

@[simp]
theorem Computation.eval_map
  {Γ : Context}
  {α : Type} {β γ : Type u}
  (f : β → γ)
  (computation : Computation Γ α β)
  (value : α)
  (state : Env Γ)
  : (f <$> computation).eval value state = f (computation.eval value state) :=
  Inputs.apply_map f computation.run (computation.inputs.read value state)

/-- Renaming preserves the values read, if every renamed reference reads the same value. -/
theorem Inputs.read_rename
  {Γ Δ : Context}
  {α : Type}
  {types : List Type}
  (rename : Renaming Γ Δ)
  (inputs : Inputs Γ α types)
  (value : α)
  (state : Env Γ)
  (renamed : Env Δ)
  (same :
    ∀ {access : Access} {β : Type} (ref : Ref Γ access β), (rename ref).get renamed = ref.get state)
  : (inputs.rename rename).read value renamed = inputs.read value state := by
  induction inputs with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Prod.mk _) ih
  | ui key _ ih => exact Prod.ext (same key) ih

theorem Computation.eval_rename
  {Γ Δ : Context}
  {α : Type}
  {β : Type u}
  (rename : Renaming Γ Δ)
  (computation : Computation Γ α β)
  (value : α)
  (state : Env Γ)
  (renamed : Env Δ)
  (same :
    ∀ {access : Access} {β : Type} (ref : Ref Γ access β), (rename ref).get renamed = ref.get state)
  : (computation.rename rename).eval value renamed = computation.eval value state := by
  simp [Computation.rename, Computation.eval, Inputs.read_rename rename _ value state renamed same]

/-- A weakened computation ignores the new innermost entry. -/
theorem Computation.eval_shift
  {Γ : Context}
  {α : Type}
  {β : Type u}
  {entry : Entry}
  (computation : Computation Γ α β)
  (value : α)
  (state : Env Γ)
  (new : entry.type)
  : (computation.rename (Renaming.shift (entry := entry))).eval value ⟨new, state⟩ =
      computation.eval value state :=
  computation.eval_rename Renaming.shift value state ⟨new, state⟩ fun _ => rfl

end Forms.Model
