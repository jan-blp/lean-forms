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

mutual
/-- Moves every placed slot along `rename`. -/
def Layout.rename
  {slots others : List Nat}
  (rename : {holes : Nat} → Slot slots holes → Slot others holes)
  : Layout slots → Layout others
  | .place slot => .place (rename slot)
  | .fill slot contents => .fill (rename slot) (Fills.rename rename contents)
  | .group label children => .group label (Layout.renameAll rename children)

def Layout.renameAll
  {slots others : List Nat}
  (rename : {holes : Nat} → Slot slots holes → Slot others holes)
  : List (Layout slots) → List (Layout others)
  | [] => []
  | child :: rest => Layout.rename rename child :: Layout.renameAll rename rest

def Fills.rename
  {slots others : List Nat}
  {holes : Nat}
  (rename : {holes : Nat} → Slot slots holes → Slot others holes)
  : Fills slots holes → Fills others holes
  | .nil => .nil
  | .cons content rest => .cons (Layout.renameAll rename content) (Fills.rename rename rest)
end

end Forms.Model
