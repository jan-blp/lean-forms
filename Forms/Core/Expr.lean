import Forms.Core.Path

namespace Forms

inductive Expr (root : DataType) : (result : DataType) → Type 1 where
  | value {t : DataType} (v : DataType.denote t) : Expr root t
  | project {t : DataType} (p : Path root t) : Expr root t
  | and (l r : Expr root .boolean) : Expr root .boolean
  | natLe (l r : Expr root .natural) : Expr root .boolean

def Expr.eval
    {root t : DataType}
    (expression : Expr root t)
    (value : DataType.denote root)
    : DataType.denote t :=
  match expression with
  | .value constant => constant
  | .project path => Path.get path value
  | .and left right => Expr.eval left value && Expr.eval right value
  | .natLe left right => decide (Expr.eval left value ≤ Expr.eval right value)

section

variable {outer root result : DataType}

def Expr.weaken {outer root result} (path : Path outer root) : Expr root result → Expr outer result
  | .value v => .value v
  | .project field => .project (path.trans field)
  | .and l r => .and (l.weaken path) (r.weaken path)
  | .natLe l r => .natLe (l.weaken path) (r.weaken path)

end

end Forms
