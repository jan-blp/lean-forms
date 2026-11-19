module

import Forms.Model.Sugar.Computation
import Tests.FormModel

open Forms.Model Forms.Model.Sugar Tests.FormModel

example :
    (compute%
      (age : Nat) ← path[Person.Field.age],
      subscribed ← path[Person.Field.subscribed]
    =>
      let adult := age ≥ 18
      subscribed && adult : Computation [] Person.Raw Bool) =
    { inputs := inputs[path[Person.Field.age], path[Person.Field.subscribed]]
      run := fun age subscribed =>
        let adult := age ≥ 18
        subscribed && adult } := rfl

example {Γ : Context} (selected : Var Γ Bool) :
    (compute%
      age ← path[Person.Field.age],
      (selected : Bool) ← .ui selected
    => selected && age ≥ 18 : Computation Γ Person.Raw Bool) =
    { inputs := inputs[path[Person.Field.age], .ui selected]
      run := fun age selected => selected && age ≥ 18 } := rfl

example :
    (compute% value ← path[] => value + 1 : Computation [] Nat Nat) =
    { inputs := inputs[path[]], run := fun value => value + 1 } := rfl

example :
    (compute% (_ : Nat) ← path[] => true : Computation [] Nat Bool) =
    { inputs := inputs[path[]], run := fun _ => true } := rfl

example :
    (compute% age ← path[Person.Field.age], subscribed <- path[Person.Field.subscribed] =>
      subscribed && age ≥ 18 : Computation [] Person.Raw Bool) =
    { inputs := inputs[path[Person.Field.age], path[Person.Field.subscribed]]
      run := fun age subscribed => subscribed && age ≥ 18 } := rfl

example :
    (compute% (value : Nat) <- path[] => value + 1 : Computation [] Nat Nat) =
    { inputs := inputs[path[]], run := fun value => value + 1 } := rfl

example : (compute% => (7 : Nat) : Computation [] Bool Nat) = .const 7 := rfl

run_cmd do
  let env ← Lean.getEnv
  match Lean.Parser.runParserCategory env `term "compute% value ← path[] => value + 1" with
  | .error message => throwError "{message}"
  | .ok _ => pure ()
  for source in [
      "compute% value ← path[] ⇒ value + 1",
      "compute% value ← path[] ↦ value + 1",
      "compute% value ← path[]"] do
    match Lean.Parser.runParserCategory env `term source with
    | .error _ => pure ()
    | .ok _ => throwError "Expected a missing ASCII separator to fail: {source}"
