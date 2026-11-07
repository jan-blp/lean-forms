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
      | .select selection => toJson ((selection.selected.val + 1) % selection.options.length)
      | .date value => toJson (Date.toString value)
    return [("argument", value)]

public def main : IO Unit := do
  let fixtures ← (FinEnum.toList Example).mapM fun selected => do
    let descriptor := CompiledFormsProtocol.descriptor compiledRevision selected
    let packed ← IO.ofExcept (CompiledFormsProtocol.openModel descriptor)
    let model := packed.2
    let controls := (CompiledView.render packed.1.definition.component model.history.value).controls
    let cases ← (controls.filter (! ·.disabled)).mapM fun control => do
      let fields ← IO.ofExcept (actionArgument control)
      let action := Json.mkObj (("key", toJson control.key.value) :: fields)
      let updated ← IO.ofExcept (CompiledFormsProtocol.actionFromJson model action >>= CompiledForms.apply model)
      pure (Json.mkObj [("action", action), ("expected", CompiledFormsProtocol.snapshotToJson (CompiledForms.snapshot updated))])
    pure (Json.mkObj [("descriptor", descriptor), ("initial", CompiledFormsProtocol.snapshotToJson (CompiledForms.snapshot model)),
      ("cases", toJson cases)])
  IO.println (toJson fixtures).compress
