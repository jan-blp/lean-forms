module

public import Forms.Model.Basic
public import Forms.Model.Context

/-! Computations declare model and context inputs and receive only their selected values. -/

@[expose] public section
namespace Forms.Model

universe u v

inductive Inputs (Γ : Context) (α : Type) : List Type → Type 1 where
  | nil : Inputs Γ α []
  | cons
      {β : Type}
      {rest : List Type}
      (path : Path α β)
      (inputs : Inputs Γ α rest)
      : Inputs Γ α (β :: rest)
  /-- Reads a context entry, whether read-only or writable. -/
  | ui {access : Access}
      {β : Type}
      {rest : List Type}
      (key : Ref Γ access β)
      (inputs : Inputs Γ α rest)
      : Inputs Γ α (β :: rest)

/-- Declares dependencies, e.g. `inputs[path[field], .ui key]`. -/
macro "inputs[" paths:term,* "]" : term => do
  let mut result ← `(Inputs.nil)
  for path in paths.getElems.reverse do
    match path with
    | `(.ui $key) => result ← `(Inputs.ui $key $result)
    | _ => result ← `(Inputs.cons $path $result)
  return result

def Inputs.weaken
  {Γ : Context}
  {α β : Type}
  {types : List Type}
  (path : Path α β)
  (inputs : Inputs Γ β types)
  : Inputs Γ α types :=
  match inputs with
  | .nil => .nil
  | .cons input rest => .cons (path.trans input) (rest.weaken path)
  | .ui key rest => .ui key (rest.weaken path)

def Inputs.Values : List Type → Type
  | [] => Unit
  | α :: rest => α × Values rest

def Inputs.Function (types : List Type) (β : Type u) : Type u :=
  match types with
  | [] => β
  | α :: rest => α → Function rest β

def Inputs.read
  {Γ : Context}
  {α : Type}
  {types : List Type}
  (inputs : Inputs Γ α types)
  (sourceValue : α)
  (state : Env Γ)
  : Values types :=
  match inputs with
  | .nil => ()
  | .cons path rest => (path.get sourceValue, rest.read sourceValue state)
  | .ui key rest => (key.get state, rest.read sourceValue state)

def Inputs.apply
  {α : Type u}
  {types : List Type}
  (fn : Function types α)
  (values : Values types)
  : α :=
  match types with
  | [] => fn
  | _ :: _ => apply (fn values.1) values.2

def Inputs.Function.map
  {types : List Type}
  {α : Type u}
  {β : Type v}
  (f : α → β)
  (fn : Function types α)
  : Function types β :=
  match types with
  | [] => f fn
  | _ :: _ => fun value => map f (fn value)

structure Computation (Γ : Context) (α : Type) (β : Type u) where
  {types : List Type}
  inputs : Inputs Γ α types
  run : Inputs.Function types β

/-- A computation without inputs. -/
def Computation.const
  {Γ : Context}
  {α : Type}
  {β : Type u}
  (value : β)
  : Computation Γ α β where
  inputs := .nil
  run := value

/-- Constant text; limited to `String` so other values never silently become constants. -/
instance {Γ : Context} {α : Type} : Coe String (Computation Γ α String) where
  coe := .const

/-- Constant tab labels. -/
instance
  {Γ : Context}
  {α : Type}
  {n : Nat}
  : Coe (Vector String n) (Computation Γ α (Vector String n)) where
  coe := .const

def Computation.eval
  {Γ : Context}
  {α : Type}
  {β : Type u}
  (computation : Computation Γ α β)
  (value : α)
  (state : Env Γ)
  : β :=
  Inputs.apply computation.run (computation.inputs.read value state)

instance {Γ : Context} {α : Type} : Functor (Computation Γ α) where
  map f computation := ⟨computation.inputs, Inputs.Function.map f computation.run⟩

def Computation.weaken
  {Γ : Context}
  {α β : Type}
  {γ : Type u}
  (path : Path α β)
  (computation : Computation Γ β γ)
  : Computation Γ α γ :=
  ⟨computation.inputs.weaken path, computation.run⟩

end Forms.Model
