import Forms.Core.Path

namespace Forms

inductive Expr : (input : DataType) → (result : DataType) → Type 1 where
  | value {input result : DataType} (v : ⟦result⟧) : Expr input result
  | project {input t : DataType} (p : Path input t) : Expr input t
  | all {input element : DataType}
      (items : Expr input (.list element))
      (predicate : Expr element .boolean)
      : Expr input .boolean
  | cases {input result : DataType} {tags : Enum} {constructors : tags → DataType}
      (subject : Expr input (.sum tags constructors))
      (branches : (i : tags) → Expr (constructors i) result) : Expr input result
  | and {input : DataType} (l r : Expr input .boolean) : Expr input .boolean
  | dateLe {input : DataType} (l r : Expr input .date) : Expr input .boolean
  | natLe {input : DataType} (l r : Expr input .natural) : Expr input .boolean

def Expr.eval
    {input t : DataType}
    (expression : Expr input t)
    (value : ⟦input⟧)
    : ⟦t⟧ :=
  match expression with
  | .value constant => constant
  | .project path => Path.get path value
  | .all items predicate => List.all (Expr.eval items value) (Expr.eval predicate)
  | .cases subject branches =>
    let selected := Expr.eval subject value
    Expr.eval (branches selected.tag) selected.payload
  | .and left right => Expr.eval left value && Expr.eval right value
  | .dateLe left right => Expr.eval left value ≤ Expr.eval right value
  | .natLe left right => Expr.eval left value ≤ Expr.eval right value

end Forms
