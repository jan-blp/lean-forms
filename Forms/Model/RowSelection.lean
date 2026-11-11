module

public import Lean.Data.Json

@[expose] public section
namespace Forms.Model

/-- The selected row, if any. -/
inductive RowSelection where
  | none
  | row (index : Nat)
  deriving Lean.ToJson, Lean.FromJson, BEq, DecidableEq, Repr

/-- Removing a row keeps the same item selected, unless that item was removed. -/
def RowSelection.remove (removed : Nat) : RowSelection → RowSelection
  | .none => .none
  | .row index =>
    if index == removed then .none
    else .row (if removed < index then index - 1 else index)

end Forms.Model
