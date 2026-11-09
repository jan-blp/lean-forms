module

import Forms.ExampleForms.FormFingerprint
meta import Forms.ExampleForms.FormFingerprint

open Lean Forms Forms.Runtime Forms.ExampleForms

private def actionArgument (input : Display.Editor) : Json :=
  match input with
  | .natural n => toJson ("00" ++ toString (n + 123456789012345678901234567890))
  | .text text => toJson (text ++ " 🌍\x00")
  | .checkbox value => toJson (!value)
  | .choice selected options => toJson ((options.find? (·.value != selected)).map (·.value) |>.getD selected)

/-- The initial snapshot, and the snapshot after applying an argument to each control. -/
private def fixture (name : String) (form : RegisteredForm) : Except String Json := do
  let (_, typed) ← form.definition.openState form.definition.initial
  let (opened, initial) ← form.open name formFingerprint form.definition.initial
  let cases ← typed.controls.mapM fun control => do
    let argument := actionArgument control.input
    let (_, expected) ← opened.execute (.apply control.key.value argument)
    pure (Json.mkObj [
      ("action", Json.mkObj [("key", toJson control.key.value), ("argument", argument)]),
      ("expected", toJson expected)])
  pure (Json.mkObj [
    ("descriptor", toJson (form.descriptor name formFingerprint)),
    ("initial", toJson initial),
    ("cases", toJson cases)])

public def main : IO Unit := do
  let fixtures ← forms.mapM fun (name, form) => IO.ofExcept (fixture name form)
  IO.println (toJson fixtures).compress
