module

public import Forms.Model.Basic
public import Forms.Model.Context

/-! Computations declare model and context inputs and receive only their selected values. -/

@[expose] public section
namespace Forms.Model

universe u v

inductive Inputs (Γ : Context) (source : Type) : List Type → Type 1 where
  | nil : Inputs Γ source []
  | cons
      {value : Type}
      {rest : List Type}
      (path : Path source value)
      (inputs : Inputs Γ source rest)
      : Inputs Γ source (value :: rest)
  /-- Reads a context entry, whether read-only or writable. -/
  | ui {access : Access}
      {value : Type}
      {rest : List Type}
      (key : Ref Γ access value)
      (inputs : Inputs Γ source rest)
      : Inputs Γ source (value :: rest)

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
  {outer source : Type}
  {types : List Type}
  (path : Path outer source)
  (inputs : Inputs Γ source types)
  : Inputs Γ outer types :=
  match inputs with
  | .nil => .nil
  | .cons input rest => .cons (path.trans input) (rest.weaken path)
  | .ui key rest => .ui key (rest.weaken path)

def Inputs.Values : List Type → Type
  | [] => Unit
  | value :: rest => value × Values rest

def Inputs.Function (types : List Type) (result : Type u) : Type u :=
  match types with
  | [] => result
  | value :: rest => value → Function rest result

def Inputs.read
  {Γ : Context}
  {source : Type}
  {types : List Type}
  (inputs : Inputs Γ source types)
  (sourceValue : source)
  (state : Env Γ)
  : Values types :=
  match inputs with
  | .nil => ()
  | .cons path rest => (path.get sourceValue, rest.read sourceValue state)
  | .ui key rest => (key.get state, rest.read sourceValue state)

def Inputs.apply
  {result : Type u}
  {types : List Type}
  (fn : Function types result)
  (values : Values types)
  : result :=
  match types with
  | [] => fn
  | _ :: _ => apply (fn values.1) values.2

def Inputs.Function.map
  {types : List Type}
  {result : Type u} {mapped : Type v}
  (f : result → mapped)
  (fn : Function types result)
  : Function types mapped :=
  match types with
  | [] => f fn
  | _ :: _ => fun value => map f (fn value)

structure Computation (Γ : Context) (source : Type) (result : Type u) where
  {types : List Type}
  inputs : Inputs Γ source types
  run : Inputs.Function types result

/-- A computation without inputs. -/
def Computation.const
  {Γ : Context}
  {source : Type}
  {result : Type u}
  (value : result)
  : Computation Γ source result where
  inputs := .nil
  run := value

def Computation.eval
  {Γ : Context}
  {source : Type} {result : Type u}
  (computation : Computation Γ source result)
  (value : source)
  (state : Env Γ)
  : result :=
  Inputs.apply computation.run (computation.inputs.read value state)

instance {Γ : Context} {source : Type} : Functor (Computation Γ source) where
  map f computation := ⟨computation.inputs, Inputs.Function.map f computation.run⟩

def Computation.weaken
  {Γ : Context}
  {outer source : Type} {result : Type u}
  (path : Path outer source)
  (computation : Computation Γ source result)
  : Computation Γ outer result :=
  ⟨computation.inputs.weaken path, computation.run⟩

end Forms.Model
