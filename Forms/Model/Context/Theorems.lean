module

public import Forms.Model.Context

public section
namespace Forms.Model

theorem Var.get_set {Γ : List Type} {α : Type} (ref : Var Γ α) (value : α) (state : Env Γ)
    : ref.get (ref.set value state) = value := by
  induction ref with
  | here => rfl
  | there ref ih => exact ih value state.tail

theorem Var.set_get {Γ : List Type} {α : Type} (ref : Var Γ α) (state : Env Γ)
    : ref.set (ref.get state) state = state := by
  induction ref with
  | here => cases state; rfl
  | there ref ih =>
    simp only [get, set, ih]
    cases state
    rfl

theorem Var.set_set {Γ : List Type} {α : Type} (ref : Var Γ α) (first second : α) (state : Env Γ)
    : ref.set second (ref.set first state) = ref.set second state := by
  induction ref with
  | here => rfl
  | there ref ih =>
    simp only [set, ih]
    rfl

end Forms.Model
