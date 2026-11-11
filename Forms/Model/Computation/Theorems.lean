module

public import Forms.Model.Computation

public section
namespace Forms.Model

universe u

/-- Evaluation depends only on the declared inputs; changes elsewhere do not affect it. -/
theorem Computation.eval_congr
  {source : Type} {result : Type u}
  (computation : Computation source result)
  (first second : source)
  (h : computation.inputs.read first = computation.inputs.read second)
  : computation.eval first = computation.eval second :=
  congrArg (Inputs.apply computation.run) h

theorem Inputs.apply_map
  {types : List Type}
  {result mapped : Type}
  (f : result → mapped)
  (fn : Inputs.Function types result)
  (values : Inputs.Values types)
  : Inputs.apply (Inputs.Function.map f fn) values = f (Inputs.apply fn values) := by
  induction types with
  | nil => rfl
  | cons _ _ ih => exact ih (fn values.1) values.2

theorem Inputs.Function.map_id
  {types : List Type}
  {result : Type}
  (fn : Inputs.Function types result)
  : Inputs.Function.map id fn = fn := by
  induction types with
  | nil =>
    rfl
  | cons _ _ ih =>
    exact funext fun value => ih (fn value)

theorem Inputs.Function.map_comp
  {types : List Type}
  {result middle mapped : Type}
  (g : result → middle)
  (h : middle → mapped)
  (fn : Inputs.Function types result)
  : Inputs.Function.map (h ∘ g) fn = Inputs.Function.map h (Inputs.Function.map g fn) := by
  induction types with
  | nil =>
    rfl
  | cons _ _ ih =>
    exact funext fun value => ih (fn value)

instance {source : Type} : LawfulFunctor (Computation source) where
  map_const := rfl
  id_map computation := by
    cases computation
    exact congrArg _ (Inputs.Function.map_id _)
  comp_map g h computation := by
    cases computation
    exact congrArg _ (Inputs.Function.map_comp g h _)

@[simp]
theorem Computation.eval_map
  {source result mapped : Type}
  (f : result → mapped)
  (computation : Computation source result)
  (value : source)
  : (f <$> computation).eval value = f (computation.eval value) :=
  Inputs.apply_map f computation.run (computation.inputs.read value)

end Forms.Model
