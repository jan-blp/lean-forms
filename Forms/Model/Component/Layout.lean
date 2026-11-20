module

public import Forms.Model.Member

@[expose] public section
namespace Forms.Model

/-- The hole count of each owned view, innermost first. -/
abbrev ViewContext := List Nat

/-- A component owned by an enclosing `own`, counted from the innermost; `holes` is its hole count. -/
abbrev ViewRef (Δ : ViewContext) (holes : Nat) := Member holes Δ

namespace ViewRef
export Member (here there)
end ViewRef

mutual
/-- Arranges the presentations in scope without owning or evaluating them. -/
inductive Layout (Δ : ViewContext) where
  | fill {holes : Nat} (view : ViewRef Δ holes) (contents : Fills Δ holes)
  | group (label : Option String) (children : List (Layout Δ))

inductive Fills (Δ : ViewContext) : (holes : Nat) → Type where
  | nil : Fills Δ 0
  | cons {holes : Nat}
      (content : List (Layout Δ))
      (rest : Fills Δ holes)
      : Fills Δ (holes + 1)
end

/-- Places a view without holes. -/
abbrev Layout.place
  {Δ : ViewContext}
  (view : ViewRef Δ 0)
  : Layout Δ :=
  .fill view .nil

mutual
def Layout.rename
  {Δ Δ' : ViewContext}
  (rename : {holes : Nat} → ViewRef Δ holes → ViewRef Δ' holes)
  : Layout Δ → Layout Δ'
  | .fill view contents => .fill (rename view) (Fills.rename rename contents)
  | .group label children => .group label (Layout.renameAll rename children)

def Layout.renameAll
  {Δ Δ' : ViewContext}
  (rename : {holes : Nat} → ViewRef Δ holes → ViewRef Δ' holes)
  : List (Layout Δ) → List (Layout Δ')
  | [] => []
  | child :: rest => Layout.rename rename child :: Layout.renameAll rename rest

def Fills.rename
  {Δ Δ' : ViewContext}
  {holes : Nat}
  (rename : {holes : Nat} → ViewRef Δ holes → ViewRef Δ' holes)
  : Fills Δ holes → Fills Δ' holes
  | .nil => .nil
  | .cons content rest => .cons (Layout.renameAll rename content) (Fills.rename rename rest)
end

end Forms.Model
