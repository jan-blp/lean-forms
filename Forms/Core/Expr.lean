import Forms.Core.Path

namespace Forms

inductive Expr : (root : DataType) → (result : DataType) → Type 1 where
  | value {root t : DataType} (v : DataType.denote t) : Expr root t
  | project {root t : DataType} (p : Path root t) : Expr root t
  | all {root element : DataType} (items : Expr root (.list element))
      (predicate : Expr element .boolean) : Expr root .boolean
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
  | .all items predicate => (items.eval value).all predicate.eval
  | .and left right => Expr.eval left value && Expr.eval right value
  | .natLe left right => decide (Expr.eval left value ≤ Expr.eval right value)

section

variable {outer root result : DataType}

def Expr.weaken {outer root result} (path : Path outer root) : Expr root result → Expr outer result
  | .value v => .value v
  | .project field => .project (path.trans field)
  | .all items predicate => .all (items.weaken path) predicate
  | .and l r => .and (l.weaken path) (r.weaken path)
  | .natLe l r => .natLe (l.weaken path) (r.weaken path)

end

end Forms
