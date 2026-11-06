module

public import Forms.Core.Dependencies

@[expose] public section

namespace Forms

theorem Expr.non_interference
  {input result : DataType}
  (expression : Expr input result)
  (left right : ⟦input⟧)
  (agree : ∀ dependency ∈ expression.dependencies.val, dependency.path.get left = dependency.path.get right)
  : expression.eval left = expression.eval right := by
  simp only [Expr.dependencies, List.mem_dedup] at agree
  induction expression with
  | all items predicate context items_ih _ =>
      have sameItems := items_ih left right (fun dependency member =>
        agree dependency (List.mem_append_left _ member))
      have sameContext := agree ⟨context⟩ (by simp [Expr.dependencies.collect])
      simp only [Expr.eval, sameItems, sameContext]
  | _ => simp_all [Expr.dependencies.collect, Expr.eval] <;> grind

end Forms
