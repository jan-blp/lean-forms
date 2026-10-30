import Forms.Core.ActionHistory
import Forms.Runtime.JsonProtocol

namespace Forms.Runtime.ActionHistoryProtocol
open Lean

def encode {state : DataType} (ids : Enum) (history : ActionHistory state ids) : Json :=
  Json.mkObj [("value", JsonProtocol.valueToJson history.value),
    ("actions", toJson (history.actions.map fun invocation => match invocation with
      | .button name => toJson (ids.label name)
      | .editor name argument => Json.mkObj [
          ("action", toJson (ids.label name)), ("argument", JsonProtocol.valueToJson argument)]))]

/-- Verify against trusted definitions and initial state; return the replay. -/
def verify {state : DataType} (ids : Enum) (definitions : ids → ActionPresentation state)
    (initial : ⟦state⟧) (submission : Json) : Except String (ActionHistory state ids) := do
  let fields ← submission.getObj?
  if fields.size != 2 then throw "Expected only value and actions in submission"
  let claimed ← JsonProtocol.valueFromJson state (← submission.getObjVal? "value")
  let actions ← (← (← submission.getObjVal? "actions").getArr?).mapM fun json => do
    let (name, argument) ← match json with
      | .str name => pure (name, none)
      | _ => do
        let fields ← json.getObj?
        if fields.size != 2 then throw "Expected only action and argument"
        let name ← (← json.getObjVal? "action").getStr?
        let argument ← JsonProtocol.valueFromJson state (← json.getObjVal? "argument")
        pure (name, some argument)
    let some action := (FinEnum.toList ids).find? (fun id => ids.label id == name)
      | throw s!"Unknown action: {name}"
    pure (match argument with
      | none => ActionInvocation.button action
      | some argument => ActionInvocation.editor action argument)
  let replayed ← ActionHistory.replay definitions initial actions
  if JsonProtocol.valueToJson replayed.value != JsonProtocol.valueToJson claimed then
    throw "Submitted value does not match action replay"
  return replayed

end Forms.Runtime.ActionHistoryProtocol
