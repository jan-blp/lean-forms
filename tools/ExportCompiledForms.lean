module

import Forms.ExampleForms.FormFingerprint
meta import Forms.ExampleForms.FormFingerprint

open Lean Forms Forms.Runtime Forms.ExampleForms

private def actionArgument (input : Display.Editor) : Json :=
  match input with
  | .text .natural text => toJson ("00" ++ toString (text.toNat! + 123456789012345678901234567890))
  | .text .plain text => toJson (text ++ " 🌍\x00")
  | .text .integer text => toJson (s!" {text.toInt! - 123456789012345678901234567890} ")
  | .text .decimal text => toJson (text ++ "05")
  | .text .date _ => toJson "2024-02-29"
  | .text .uuid _ => toJson "123E4567-E89B-12D3-A456-426614174000"
  | .checkbox value => toJson (!value)
  | .action => Json.null
  | .tabs active labels => toJson (toString ((active + 1) % labels.length.max 1))
  | .choice selected options => toJson ((options.find? (·.value != selected)).map (·.value) |>.getD selected)
  | .choices selected options =>
    let toggled := (options.head?.map (·.value)).getD ""
    let picked (value : String) := (value == toggled) != selected.contains value
    toJson ((options.map (·.value)).filter picked)

/-- The initial snapshot, and the snapshot after applying an argument to each control. -/
private def fixture (name : String) (form : RegisteredForm) : Except String Json := do
  let (_, typed) ← form.definition.openState form.definition.initial
  let (opened, initial) ← form.open name formFingerprint form.definition.initial
  let cases ← typed.controls.mapM fun control => do
    let argument := actionArgument control.input
    let key := ControlKeyProtocol.toString control.key
    let (_, expected) ← opened.execute (.apply key argument)
    pure (Json.mkObj [
      ("action", Json.mkObj [("key", toJson key), ("argument", argument)]),
      ("expected", toJson expected)])
  pure (Json.mkObj [
    ("start", toJson (form.start name formFingerprint)),
    ("initial", toJson initial),
    ("cases", toJson cases)])

public def main : IO Unit := do
  let fixtures ← forms.mapM fun (name, form) => IO.ofExcept (fixture name form)
  IO.println (toJson fixtures).compress
