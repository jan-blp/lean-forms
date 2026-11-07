module

import Forms.Runtime.CompiledRevision
meta import Forms.Runtime.CompiledRevision

open Lean Forms Forms.Runtime Forms.ExampleForms

private def actionArgument (control : CompiledView.Control) : Except String (List (String × Json)) := do
  if control.kind == "button" then return []
  if control.kind == "choice" then
    let options ← (← control.view.getObjVal? "options").getArr?
    return [("argument", options.toList.getLast!)]
  let current ← control.view.getObjVal? "value"
  let kind ← control.view.getObjValAs? String "widget"
  let value ← match kind with
    | "naturalInput" => do
      let n ← JsonProtocol.valueFromJson .natural current
      pure (toJson ("00" ++ toString (n + 123456789012345678901234567890)))
    | "textInput" => current.getStr?.map fun text => toJson (text ++ " 🌍\x00")
    | "checkbox" => current.getBool?.map fun value => toJson (!value)
    | "select" => do
      let options ← (← control.view.getObjVal? "options").getArr?
      pure (toJson (((← current.getNat?) + 1) % options.size))
    | _ => pure current
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
