module

@[expose] public section
namespace Forms.Model

/-- A reference to a variable in a typed context. -/
inductive Var : (Γ : List Type) → Type → Type 1 where
  | here {α : Type} {Γ : List Type} : Var (α :: Γ) α
  | there {α β : Type} {Γ : List Type} (ref : Var Γ α) : Var (β :: Γ) α

structure Binding (α rest : Type) where
  value : α
  tail : rest

/-- Values for every variable in a typed context. -/
def Env : List Type → Type
  | [] => Unit
  | α :: Γ => Binding α (Env Γ)

variable {α : Type}

abbrev Env.nil : Env [] := ()
abbrev Env.cons {Γ : List Type} (value : α) (tail : Env Γ) : Env (α :: Γ) :=
  ⟨value, tail⟩

macro "env[" values:term,* "]" : term => do
  let mut result ← `(Env.nil)
  for value in values.getElems.reverse do
    result ← `(Env.cons $value $result)
  return result

def Var.get {Γ : List Type} (ref : Var Γ α) (state : Env Γ) : α :=
  match ref with
  | .here => state.value
  | .there ref => ref.get state.tail

def Var.set {Γ : List Type} (ref : Var Γ α) (value : α) (state : Env Γ) : Env Γ :=
  match ref with
  | .here => ⟨value, state.tail⟩
  | .there ref => ⟨state.value, ref.set value state.tail⟩

/-- Identifies the UI variable in control keys sent to the frontend. -/
def Var.index {Γ : List Type} : Var Γ α → Nat
  | .here => 0
  | .there ref => ref.index + 1

end Forms.Model
