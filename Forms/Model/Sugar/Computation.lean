module

public import Forms.Model.Computation
public meta import Lean.Elab.Term

public meta section
namespace Forms.Model.Sugar
open Lean

declare_syntax_cat computationInput
syntax binderIdent unicode(" ← ", " <- ") term : computationInput
syntax "(" binderIdent " : " term ")" unicode(" ← ", " <- ") term : computationInput

/--
`compute% (x : T) ← input, … => body` reads each input into its binder and evaluates `body`.
Types are optional; use `.ui ref[name]` to read context inputs inside `named%`.
-/
scoped syntax "compute% " computationInput,* " => " term : term

macro_rules
  | `(compute% $bindings:computationInput,* => $body) => do
    let mut inputs : Array Term := #[]
    let mut run := body
    for binding in bindings.getElems.reverse do
      match binding with
      | `(computationInput| $name:binderIdent ← $input) =>
        inputs := inputs.push input
        run ← `(fun ($(⟨name.raw[0]⟩) : _) => $run)
      | `(computationInput| ($name:binderIdent : $type) ← $input) =>
        inputs := inputs.push input
        run ← `(fun ($(⟨name.raw[0]⟩) : $type) => $run)
      | _ => Macro.throwUnsupported
    `({ inputs := inputs[$(inputs.reverse),*], run := $run : Computation _ _ _ })

end Forms.Model.Sugar
