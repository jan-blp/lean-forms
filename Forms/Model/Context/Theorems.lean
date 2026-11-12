module

public import Forms.Model.Context

public section
namespace Forms.Model

theorem Var.get_set
  {Γ : Context}
  {α : Type}
  (ref : Var Γ α)
  (value : α)
  (state : Env Γ)
  : ref.get (ref.set value state) = value := by
  induction Γ generalizing α with
  | nil => cases ref
  | cons entry Γ ih =>
    cases ref with
    | here => rfl
    | there ref => exact ih ref value state.tail

theorem Var.set_get
  {Γ : Context}
  {α : Type}
  (ref : Var Γ α)
  (state : Env Γ)
  : ref.set (ref.get state) state = state := by
  induction Γ generalizing α with
  | nil => cases ref
  | cons entry Γ ih =>
    cases ref with
    | here => cases state; rfl
    | there ref =>
      simp only [Ref.get, Ref.set, ih]
      cases state
      rfl

theorem Var.set_set
  {Γ : Context}
  {α : Type}
  (ref : Var Γ α)
  (first second : α)
  (state : Env Γ)
  : ref.set second (ref.set first state) = ref.set second state := by
  induction Γ generalizing α with
  | nil => cases ref
  | cons entry Γ ih =>
    cases ref with
    | here => rfl
    | there ref =>
      simp only [Ref.set, ih]
      rfl

/-- Updating writable state preserves every read-only input. -/
theorem Ref.get_set_readOnly
  {Γ : Context}
  {α β : Type}
  (input : InputRef Γ α)
  (target : Var Γ β)
  (value : β)
  (env : Env Γ)
  : input.get (target.set value env) = input.get env := by
  induction Γ generalizing α β with
  | nil => cases input
  | cons entry Γ ih =>
    cases input <;> cases target <;> grind [Ref.get, Ref.set]

end Forms.Model
