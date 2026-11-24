module

public import Forms.Model.Member
public import Forms.Model.PointedList
public import Forms.Model.Collection

@[expose] public section
namespace Forms.Model

/-- Access enforcement relies on modifying the environment only through `Ref.set`. -/
inductive Access where
  | readOnly
  | writable

structure Entry where
  access : Access
  type : Type

abbrev Context := List Entry

abbrev Ref (Γ : Context) (access : Access) (α : Type) := Member (⟨access, α⟩ : Entry) Γ

namespace Ref
export Member (here)
end Ref

abbrev Ref.there
  {Γ : Context}
  {entry : Entry}
  {access : Access}
  {α : Type}
  (ref : Ref Γ access α)
  : Ref (entry :: Γ) access α :=
  Member.there ref

abbrev Var (Γ : Context) (α : Type) := Ref Γ .writable α

abbrev InputRef (Γ : Context) (α : Type) := Ref Γ .readOnly α

abbrev Context.row (α : Type) (Γ : Context) : Context :=
  ⟨.readOnly, PointedList (Item α)⟩ -- the entries and the row's index
  :: ⟨.writable, Bool⟩ -- whether to remove the row
  :: Γ

abbrev Ref.row {α : Type} {Γ : Context} : InputRef (Context.row α Γ) (PointedList (Item α)) := .here

abbrev Ref.rowRemoved {α : Type} {Γ : Context} : Var (Context.row α Γ) Bool := .there .here

structure Binding (α β : Type) where
  value : α
  tail : β

def Env : Context → Type
  | [] => Unit
  | entry :: Γ => Binding entry.type (Env Γ)

variable {Γ : Context} {α : Type} {access : Access}

abbrev Env.nil : Env [] := ()
abbrev Env.cons (value : α) (tail : Env Γ) : Env (⟨access, α⟩ :: Γ) :=
  ⟨value, tail⟩

abbrev Env.row
  {β : Type}
  (items : List (Item β))
  (index : Fin items.length)
  (env : Env Γ)
  : Env (Context.row β Γ) :=
  Env.cons ⟨items, index⟩ (Env.cons false env)

macro "env[" values:term,* "]" : term => do
  let mut result ← `(Env.nil)
  for value in values.getElems.reverse do
    result ← `(Env.cons $value $result)
  return result

def Ref.get
  {Γ : Context}
  (ref : Ref Γ access α)
  (env : Env Γ)
  : α :=
  match ref with
  | .here => env.value
  | .there ref => Ref.get ref env.tail

def Ref.set
  {Γ : Context}
  (ref : Var Γ α)
  (value : α)
  (env : Env Γ)
  : Env Γ :=
  match ref with
  | .here => ⟨value, env.tail⟩
  | .there ref => ⟨env.value, Ref.set ref value env.tail⟩

abbrev Renaming (Γ Δ : Context) := ∀ {access : Access} {α : Type}, Ref Γ access α → Ref Δ access α

def Renaming.lift
  {Γ Δ : Context}
  {entry : Entry}
  (rename : Renaming Γ Δ)
  : Renaming (entry :: Γ) (entry :: Δ) := fun
  | .here => .here
  | .there ref => .there (rename ref)

def Renaming.liftRow
  {α : Type}
  {Γ Δ : Context}
  (rename : Renaming Γ Δ)
  : Renaming (Context.row α Γ) (Context.row α Δ) :=
  Renaming.lift (Renaming.lift rename)

def Renaming.shift {Γ : Context} {entry : Entry} : Renaming Γ (entry :: Γ) :=
  .there

def Renaming.row {α : Type} {Γ : Context} : Renaming Γ (Context.row α Γ) :=
  fun ref => .there (.there ref)

end Forms.Model
