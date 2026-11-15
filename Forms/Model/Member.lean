module

@[expose] public section
namespace Forms.Model

universe u

/-- `List.Mem` in `Type`, so it carries a position. -/
inductive Member {α : Type u} (a : α) : List α → Type u where
  | here {rest : List α} : Member a (a :: rest)
  | there {b : α} {rest : List α} (member : Member a rest) : Member a (b :: rest)

end Forms.Model
