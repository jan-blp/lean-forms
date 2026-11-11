module

public import Forms.Model.Computation

public section
namespace Forms.Model

/-- Evaluation depends only on the declared inputs; changes elsewhere do not affect it. -/
theorem Computation.eval_congr
  {source result : Type}
  (computation : Computation source result)
  (first second : source)
  (h : computation.inputs.read first = computation.inputs.read second)
  : computation.eval first = computation.eval second :=
  congrArg (Inputs.apply computation.run) h

end Forms.Model
