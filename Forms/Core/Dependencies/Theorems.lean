module

public import Forms.Core.Dependencies

@[expose] public section

namespace Forms

theorem Expr.non_interference
  {input result : DataType}
  (expression : Expr input result)
  (left right : ⟦input⟧)
  (agree : ∀ dependency ∈ expression.dependencies, dependency.path.get left = dependency.path.get right)
  : expression.eval left = expression.eval right := by
  induction expression <;> simp_all [Expr.dependencies, Expr.eval] <;> grind

end Forms
