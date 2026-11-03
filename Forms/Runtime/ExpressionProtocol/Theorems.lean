import Forms.Runtime.ExpressionProtocol.ExpressionTheorems

namespace Forms.Runtime.ExpressionProtocol

/-- Serializing the input type, expression and value preserves evaluation for every
expression constructor and data type, including nested records, sums and lists. -/
theorem evaluate_preserved {input result : DataType}
    (expression : Forms.Expr input result) (value : ⟦input⟧) :
    evaluate input.toJson expression.toJson (JsonProtocol.valueToJson value) =
      .ok (JsonProtocol.valueToJson (expression.eval value)) := by
  simp [evaluate, evaluateTyped, schema_decode, expression_decode, value_decode,
    canonicalExpr_eval, canonicalValue_toJson, bind, Except.bind, pure, Except.pure,
    Except.map]

end Forms.Runtime.ExpressionProtocol
