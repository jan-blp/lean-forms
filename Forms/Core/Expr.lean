import Forms.Core.Path

namespace Forms

inductive Expr (input : DataType) : (result : DataType) → Type where
  | value {t : DataType} (v : ⟦t⟧) : Expr input t
  | project {t : DataType} (p : Path input t) : Expr input t
  | and (l r : Expr input .boolean) : Expr input .boolean
  | natLe (l r : Expr input .natural) : Expr input .boolean

def Expr.eval
    {input type : DataType}
    (expression : Expr input type)
    (value : ⟦input⟧)
    : ⟦type⟧ :=
  match expression with
  | .value constant => constant
  | .project path => Path.get path value
  | .and left right => Expr.eval left value && Expr.eval right value
  | .natLe left right => Expr.eval left value ≤ Expr.eval right value

end Forms
