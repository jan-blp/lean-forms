import Forms.Core.Expr

namespace Forms

/-- A typed update to local form state. -/
inductive Action : DataType → Type 1 where
  | set {state value : DataType}
    (target : Path state value)
    (replacement : Expr state value)
    : Action state
  | append {state element : DataType}
    (target : Path state (.list element))
    (value : Expr state element)
    : Action state

inductive Action.Button where
  | press

def Action.increment {state : DataType}
  (target : Path state .natural)
  : Action state :=
  .set target (.natAdd (.project target) (.value 1))

def Action.decrement {state : DataType}
  (target : Path state .natural)
  : Action state :=
  .set target (.natSub (.project target) (.value 1))

def Action.eval {state : DataType}
  (action : Action state)
  (value : ⟦state⟧)
  : ⟦state⟧ :=
  match action with
  | .set target replacement => target.set (replacement.eval value) value
  | .append target expression => target.set (target.get value ++ [expression.eval value]) value

def Action.weaken {outer inner : DataType}
  (path : Path outer inner)
  : Action inner → Action outer
  | .set target replacement => .set (path.trans target) (replacement.weaken path)
  | .append target expression => .append (path.trans target) (expression.weaken path)

end Forms
