module

public import Forms.Model.Member

@[expose] public section
namespace Forms.Model

/-- A component owned by an enclosing `own`, counted from the innermost.
`owned` gives the hole count of each view in scope, innermost first; `holes` is this one's. -/
abbrev ViewRef (owned : List Nat) (holes : Nat) := Member holes owned

namespace ViewRef
export Member (here there)
end ViewRef

mutual
/-- Arranges the presentations in scope without owning or evaluating them. -/
inductive Layout (owned : List Nat) where
  | fill {holes : Nat} (view : ViewRef owned holes) (contents : Fills owned holes)
  | group (label : Option String) (children : List (Layout owned))

inductive Fills (owned : List Nat) : (holes : Nat) → Type where
  | nil : Fills owned 0
  | cons {holes : Nat}
      (content : List (Layout owned))
      (rest : Fills owned holes)
      : Fills owned (holes + 1)
end

/-- Places a view without holes. -/
abbrev Layout.place
  {owned : List Nat}
  (view : ViewRef owned 0)
  : Layout owned :=
  .fill view .nil

mutual
def Layout.rename
  {owned others : List Nat}
  (rename : {holes : Nat} → ViewRef owned holes → ViewRef others holes)
  : Layout owned → Layout others
  | .fill view contents => .fill (rename view) (Fills.rename rename contents)
  | .group label children => .group label (Layout.renameAll rename children)

def Layout.renameAll
  {owned others : List Nat}
  (rename : {holes : Nat} → ViewRef owned holes → ViewRef others holes)
  : List (Layout owned) → List (Layout others)
  | [] => []
  | child :: rest => Layout.rename rename child :: Layout.renameAll rename rest

def Fills.rename
  {owned others : List Nat}
  {holes : Nat}
  (rename : {holes : Nat} → ViewRef owned holes → ViewRef others holes)
  : Fills owned holes → Fills others holes
  | .nil => .nil
  | .cons content rest => .cons (Layout.renameAll rename content) (Fills.rename rename rest)
end

end Forms.Model
