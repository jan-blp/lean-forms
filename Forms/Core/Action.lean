module

public import Forms.Core.Path

@[expose] public section

namespace Forms

/-- A typed update to local form state. -/
inductive Action : DataType → Type 1 where
  | set {state value : DataType}
    (target : Path state value)
    (replacement : ⟦state⟧ → ⟦value⟧)
    : Action state

inductive Action.Button where
  | press

def Action.append {state element : DataType}
  (target : Path state (.list element))
  (value : ⟦state⟧ → ⟦element⟧)
  : Action state :=
  .set target (fun state => target.get state ++ [value state])

def Action.increment {state : DataType}
  (target : Path state .natural)
  : Action state :=
  .set target (fun state => target.get state + 1)

def Action.decrement {state : DataType}
  (target : Path state .natural)
  : Action state :=
  .set target (fun state => target.get state - 1)

def Action.eval {state : DataType}
  (action : Action state)
  (value : ⟦state⟧)
  : ⟦state⟧ :=
  match action with
  | .set target replacement => target.set (replacement value) value

def Action.weaken {outer inner : DataType}
  (path : Path outer inner)
  : Action inner → Action outer
  | .set target replacement => .set (path.trans target) (replacement ∘ path.get)

end Forms
