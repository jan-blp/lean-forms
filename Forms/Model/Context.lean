module

@[expose] public section
namespace Forms.Model

/-- Whether UI actions may update a context entry.
NOTE: Access enforcement relies on modifying the environment only through `Ref.set`. -/
inductive Access where
  | readOnly
  | writable

structure Entry where
  access : Access
  type : Type

/-- Entries in scope. -/
abbrev Context := List Entry

/-- A reference to a context entry, tracking its access and value type. -/
inductive Ref : (Γ : Context) → Access → Type → Type 1 where
  | here {access : Access} {α : Type} {Γ : Context}
      : Ref (⟨access, α⟩ :: Γ) access α
  | there {access : Access} {α : Type} {entry : Entry} {Γ : Context}
      (ref : Ref Γ access α)
      : Ref (entry :: Γ) access α

/-- A reference to writable state in a typed context. -/
abbrev Var (Γ : Context) (α : Type) := Ref Γ .writable α

/-- A reference to a read-only input in a typed context. -/
abbrev InputRef (Γ : Context) (α : Type) := Ref Γ .readOnly α

structure Binding (α β : Type) where
  value : α
  tail : β

/-- Values for every entry in a typed context. -/
def Env : Context → Type
  | [] => Unit
  | entry :: Γ => Binding entry.type (Env Γ)

variable {Γ : Context} {α : Type} {access : Access}

abbrev Env.nil : Env [] := ()
abbrev Env.cons (value : α) (tail : Env Γ) : Env (⟨access, α⟩ :: Γ) :=
  ⟨value, tail⟩

macro "env[" values:term,* "]" : term => do
  let mut result ← `(Env.nil)
  for value in values.getElems.reverse do
    result ← `(Env.cons $value $result)
  return result

/-- Reads a reference. -/
def Ref.get
  {Γ : Context}
  (ref : Ref Γ access α)
  (env : Env Γ)
  : α :=
  match ref with
  | .here => env.value
  | .there ref => ref.get env.tail

/-- Updates writable state. -/
def Ref.set
  {Γ : Context}
  (ref : Var Γ α)
  (value : α)
  (env : Env Γ)
  : Env Γ :=
  match ref with
  | .here => ⟨value, env.tail⟩
  | .there ref => ⟨env.value, ref.set value env.tail⟩

/-- Maps every reference into another context, keeping its access and type. -/
abbrev Renaming (Γ Δ : Context) := ∀ {access : Access} {α : Type}, Ref Γ access α → Ref Δ access α

/-- Leaves the innermost entry in place and renames the rest. -/
def Renaming.lift
  {Γ Δ : Context}
  {entry : Entry}
  (rename : Renaming Γ Δ)
  : Renaming (entry :: Γ) (entry :: Δ)
  | _, _, .here => .here
  | _, _, .there ref => .there (rename ref)

/-- Makes room for a new innermost entry. -/
def Renaming.shift {Γ : Context} {entry : Entry} : Renaming Γ (entry :: Γ) :=
  .there

/-- Identifies the context entry in control keys sent to the frontend. -/
def Ref.index {Γ : Context} (ref : Ref Γ access α) : Nat :=
  match ref with
  | .here => 0
  | .there ref => ref.index + 1

end Forms.Model
