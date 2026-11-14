module

public import Forms.Model.Member

@[expose] public section
namespace Forms.Model

/-- A component owned by an enclosing `own`, counted from the innermost.
`slots` gives the hole count of each slot in scope, innermost first; `holes` is this one's. -/
abbrev Slot (slots : List Nat) (holes : Nat) := Member holes slots

namespace Slot
export Member (here there)
end Slot

mutual
/-- Arranges the presentations in scope without owning or evaluating them. -/
inductive Layout (slots : List Nat) where
  | place (slot : Slot slots 0)
  /-- Places `slot` with `contents` in its holes. -/
  | fill {holes : Nat} (slot : Slot slots holes) (contents : Fills slots holes)
  | group (label : Option String) (children : List (Layout slots))

/-- Content for each hole of a placed presentation, in order. -/
inductive Fills (slots : List Nat) : (holes : Nat) → Type where
  | nil : Fills slots 0
  | cons {holes : Nat}
      (content : List (Layout slots))
      (rest : Fills slots holes)
      : Fills slots (holes + 1)
end

end Forms.Model
