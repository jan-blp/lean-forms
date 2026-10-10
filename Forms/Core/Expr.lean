import Forms.Core.Path

namespace Forms

inductive Expr : (root : DataType) → (result : DataType) → Type 1 where
  | value {root result : DataType} (v : DataType.denote result) : Expr root result
  | project {root t : DataType} (p : Path root t) : Expr root t
  | all {root element : DataType}
      (items : Expr root (.list element))
      (predicate : Expr element .boolean)
      : Expr root .boolean
  | and {root : DataType} (l r : Expr root .boolean) : Expr root .boolean
  | natLe {root : DataType} (l r : Expr root .natural) : Expr root .boolean

def Expr.eval
    {root t : DataType}
    (expression : Expr root t)
    (value : DataType.denote root)
    : DataType.denote t :=
  match expression with
  | .value constant => constant
  | .project path => Path.get path value
  | .all items predicate => List.all (Expr.eval items value) (Expr.eval predicate)
  | .and left right => Expr.eval left value && Expr.eval right value
  | .natLe left right => decide (Expr.eval left value ≤ Expr.eval right value)

section

variable {outer root result : DataType}

def Expr.weaken {outer root result} (path : Path outer root) (expression : Expr root result) : Expr outer result :=
  match expression with
  | .value v => .value v
  | .project field => .project (Path.trans path field)
  | .all items predicate => .all (Expr.weaken path items) predicate
  | .and l r => .and (Expr.weaken path l) (Expr.weaken path r)
  | .natLe l r => .natLe (Expr.weaken path l) (Expr.weaken path r)

end

end Forms
