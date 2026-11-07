module

import Forms.Runtime.CompiledRevision
meta import Forms.Runtime.CompiledRevision

open Lean Forms Forms.Runtime Forms.ExampleForms

private def actionArgument {α : Type} (control : CompiledView.Control α) : Except String (List (String × Json)) := do
  match control.view.body with
  | .button _ => return []
  | .choice _ _ options => return [("argument", toJson options.getLast!)]
  | .editor _ input =>
    let value := match input with
      | .natural n => toJson ("00" ++ toString (n + 123456789012345678901234567890))
      | .text text => toJson (text ++ " 🌍\x00")
      | .checkbox value => toJson (!value)
      | .select value options => toJson ((value + 1) % options.length)
      | .date value => toJson (Date.toString value)
    return [("argument", value)]

public def main : IO Unit := do
  let fixtures ← (FinEnum.toList Example).mapM fun selected => do
    let descriptor := CompiledForms.descriptor compiledRevision selected
    let packed ← IO.ofExcept (CompiledForms.openModel descriptor)
    let model := packed.2
    let controls := (CompiledView.render packed.1.definition.component model.history.value).controls
    let cases ← (controls.filter (! ·.disabled)).mapM fun control => do
      let fields ← IO.ofExcept (actionArgument control)
      let action := Json.mkObj (("key", toJson control.key) :: fields)
      let updated ← IO.ofExcept (CompiledForms.apply model action)
      pure (Json.mkObj [("action", action), ("expected", CompiledForms.snapshot updated)])
    pure (Json.mkObj [("descriptor", descriptor), ("initial", CompiledForms.snapshot model),
      ("cases", toJson cases)])
  IO.println (toJson fixtures).compress
