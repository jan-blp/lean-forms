module

import Forms.ExampleForms.FormFingerprint
meta import Forms.ExampleForms.FormFingerprint

open Lean Forms Forms.Runtime Forms.ExampleForms

private def actionArgument (input : Display.Editor) : Json :=
  match input with
  | .field (.text .natural text) _ =>
    toJson ("00" ++ toString (text.toNat! + 123456789012345678901234567890))
  | .field (.text .plain text) _ => toJson (text ++ " 🌍\x00")
  | .field (.text .integer text) _ => toJson (s!" {text.toInt! - 123456789012345678901234567890} ")
  | .field (.text .decimal text) _ => toJson (text ++ "05")
  | .field (.text .date _) _ => toJson "2024-02-29"
  | .field (.text .uuid _) _ => toJson "123E4567-E89B-12D3-A456-426614174000"
  | .field (.checkbox value) _ => toJson (!value)
  | .action => Json.null
  | .tabs active labels => toJson (toString ((active + 1) % labels.length.max 1))
  | .lookup .. => Json.mkObj [("lookup", toJson (LookupInput.search "a"))]
  | .choice selected options => toJson ((options.find? (·.value != selected)).map (·.value) |>.getD selected)
  | .field (.choices selected options) _ =>
    let toggled := (options.head?.map (·.value)).getD ""
    let picked (value : String) := (value == toggled) != selected.contains value
    toJson ((options.map (·.value)).filter picked)

private def seed : String :=
  "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"

/-- The initial snapshot, and the snapshot after applying an argument to each control. -/
private def fixture (name : String) (form : RegisteredForm) : Except String Json := do
  let some supply := Model.Supply.ofSeed? seed | throw "Invalid seed"
  let settings := settingsFor name
  let typed := (← form.definition.openState form.definition.initial settings supply).snapshot
  let opened ← form.open name formFingerprint form.definition.initial settings supply
  let cases ← typed.controls.mapM fun control => do
    let argument := actionArgument control.input
    let key := ControlKeyProtocol.toString control.key
    let (_, expected) ← opened.form.execute (.apply key argument)
    pure (Json.mkObj [
      ("action", Json.mkObj [("key", toJson key), ("argument", argument)]),
      ("expected", toJson expected)])
  pure (Json.mkObj [
    ("start", toJson (form.start name formFingerprint settings)),
    ("seed", toJson seed),
    ("initial", toJson opened.snapshot),
    ("cases", toJson cases)])

public def main : IO Unit := do
  let fixtures ← forms.mapM fun (name, form) => IO.ofExcept (fixture name form)
  IO.println (toJson fixtures).compress
