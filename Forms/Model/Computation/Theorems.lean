module

public import Forms.Model.Computation

public section
namespace Forms.Model

universe u v w

/-- Evaluation depends only on the declared inputs; changes elsewhere do not affect it. -/
theorem Computation.eval_congr
  {Γ : List Type}
  {source : Type} {result : Type u}
  (computation : Computation Γ source result)
  (first second : source)
  (firstState secondState : Env Γ)
  (h : computation.inputs.read first firstState = computation.inputs.read second secondState)
  : computation.eval first firstState = computation.eval second secondState :=
  congrArg (Inputs.apply computation.run) h

theorem Inputs.apply_map
  {types : List Type}
  {result : Type u} {mapped : Type v}
  (f : result → mapped)
  (fn : Inputs.Function types result)
  (values : Inputs.Values types)
  : Inputs.apply (Inputs.Function.map f fn) values = f (Inputs.apply fn values) := by
  induction types with
  | nil => rfl
  | cons _ _ ih => exact ih (fn values.1) values.2

theorem Inputs.Function.map_id
  {types : List Type}
  {result : Type u}
  (fn : Inputs.Function types result)
  : Inputs.Function.map id fn = fn := by
  induction types with
  | nil =>
    rfl
  | cons _ _ ih =>
    exact funext fun value => ih (fn value)

theorem Inputs.Function.map_comp
  {types : List Type}
  {result : Type u} {middle : Type v} {mapped : Type w}
  (g : result → middle)
  (h : middle → mapped)
  (fn : Inputs.Function types result)
  : Inputs.Function.map (h ∘ g) fn = Inputs.Function.map h (Inputs.Function.map g fn) := by
  induction types with
  | nil =>
    rfl
  | cons _ _ ih =>
    exact funext fun value => ih (fn value)

instance {Γ : List Type} {source : Type} : LawfulFunctor (Computation Γ source) where
  map_const := rfl
  id_map computation := by
    cases computation
    exact congrArg _ (Inputs.Function.map_id _)
  comp_map g h computation := by
    cases computation
    exact congrArg _ (Inputs.Function.map_comp g h _)

@[simp]
theorem Computation.eval_map
  {Γ : List Type}
  {source : Type} {result mapped : Type u}
  (f : result → mapped)
  (computation : Computation Γ source result)
  (value : source)
  (state : Env Γ)
  : (f <$> computation).eval value state = f (computation.eval value state) :=
  Inputs.apply_map f computation.run (computation.inputs.read value state)

end Forms.Model
