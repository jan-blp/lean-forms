module

@[expose] public section
namespace Forms.Model

/-- A presentation owned by an enclosing `own`, counted from the innermost one. -/
inductive Slot : Nat → Type where
  | here {slots : Nat} : Slot (slots + 1)
  | there {slots : Nat} (slot : Slot slots) : Slot (slots + 1)
  deriving DecidableEq

/-- Arranges the presentations in scope without owning or evaluating them. -/
inductive Layout (slots : Nat) where
  | place (slot : Slot slots)
  | group (label : Option String) (children : List (Layout slots))

end Forms.Model
