module

public import Forms.Model.Basic

/-! Computations declare typed input paths and receive only the selected values. -/

@[expose] public section
namespace Forms.Model

inductive Inputs (source : Type) : List Type → Type 1 where
  | nil : Inputs source []
  | cons
      {value : Type}
      {rest : List Type}
      (path : Path source value)
      (inputs : Inputs source rest)
      : Inputs source (value :: rest)

macro "inputs[" paths:term,* "]" : term => do
  let mut result ← `(Inputs.nil)
  for path in paths.getElems.reverse do
    result ← `(Inputs.cons $path $result)
  return result

def Inputs.weaken
  {outer source : Type}
  {types : List Type}
  (path : Path outer source)
  (inputs : Inputs source types)
  : Inputs outer types :=
  match inputs with
  | .nil => .nil
  | .cons input rest => .cons (path.trans input) (rest.weaken path)

def Inputs.Values : List Type → Type
  | [] => Unit
  | value :: rest => value × Values rest

def Inputs.Function (types : List Type) (result : Type) : Type :=
  match types with
  | [] => result
  | value :: rest => value → Function rest result

def Inputs.read
  {source : Type}
  {types : List Type}
  (inputs : Inputs source types)
  (sourceValue : source)
  : Values types :=
  match inputs with
  | .nil => ()
  | .cons path rest => (path.get sourceValue, rest.read sourceValue)

def Inputs.apply
  {result : Type}
  {types : List Type}
  (fn : Function types result)
  (values : Values types)
  : result :=
  match types with
  | [] => fn
  | _ :: _ => apply (fn values.1) values.2

def Inputs.Function.map
  {types : List Type}
  {result mapped : Type}
  (f : result → mapped)
  (fn : Function types result)
  : Function types mapped :=
  match types with
  | [] => f fn
  | _ :: _ => fun value => map f (fn value)

structure Computation (source result : Type) where
  {types : List Type}
  inputs : Inputs source types
  run : Inputs.Function types result

/-- A computation without inputs. -/
def Computation.const {source result : Type} (value : result) : Computation source result where
  inputs := .nil
  run := value

def Computation.eval
  {source result : Type}
  (computation : Computation source result)
  (value : source)
  : result :=
  Inputs.apply computation.run (computation.inputs.read value)

instance {source : Type} : Functor (Computation source) where
  map f computation := ⟨computation.inputs, Inputs.Function.map f computation.run⟩

def Computation.weaken
  {outer source result : Type}
  (path : Path outer source)
  (computation : Computation source result)
  : Computation outer result :=
  ⟨computation.inputs.weaken path, computation.run⟩

end Forms.Model
