module

import Forms.Runtime.CompiledRevision
meta import Forms.Runtime.CompiledRevision

open Lean Forms Forms.Runtime Forms.ExampleForms

private def actionArgument {α : Type} (control : ModelView.Control α) : Except String (List (String × Json)) := do
  let .editor _ input := control.view.body
  let value := match input with
    | .natural n => toJson ("00" ++ toString (n + 123456789012345678901234567890))
    | .text text => toJson (text ++ " 🌍\x00")
    | .checkbox value => toJson (!value)
  return [("argument", value)]

public def main : IO Unit := do
  let state := ModelForm.openState TypedPerson.initial
  let controls := (ModelView.render TypedPerson.form state.value).controls
  let cases ← controls.mapM fun control => do
    let fields ← IO.ofExcept (actionArgument control)
    let action := Json.mkObj (("key", toJson control.key.value) :: fields)
    let (updated, _) ← IO.ofExcept (TypedPersonProtocol.execute state
      (.apply control.key.value ((fields.lookup "argument").getD Json.null)))
    pure (Json.mkObj [("action", action), ("expected", toJson (TypedPersonProtocol.snapshot updated))])
  let typed := Json.mkObj [
    ("descriptor", TypedPersonProtocol.descriptor compiledRevision),
    ("initial", toJson (TypedPersonProtocol.snapshot state)), ("cases", toJson cases)]
  IO.println (toJson [typed]).compress
