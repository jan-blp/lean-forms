module

public import LeanLens.Lawful

@[expose] public section
namespace Forms.Model
open LeanLens

theorem lawfulMkLens
  {s a : Type}
  {get : s → a}
  {put : a → s → s}
  (view_set : ∀ v src, get (put v src) = v := by intros; rfl)
  (set_view : ∀ src, put (get src) src = src := by intros; rfl)
  (set_set : ∀ v v' src, put v' (put v src) = put v' src := by intros; rfl)
  : LawfulLens (mkLens get put) :=
  ⟨view_set, set_view, set_set⟩

end Forms.Model
