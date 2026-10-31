import Forms.Core.ComponentHistory
import Forms.Runtime.JsonProtocol

namespace Forms.Runtime.ComponentHistoryProtocol
open Lean Composition

private def invocationToJson {ty : DataType} (component : Component ty)
    (target : List String) : component.Invocation → Json :=
  match component with
  | .actionWidget (ids := ids) .. => fun invocation =>
      Json.mkObj ([("target", toJson target)] ++ match invocation with
        | .button name => [("action", toJson (ids.label name))]
        | .editor name argument => [("action", toJson (ids.label name)),
            ("argument", JsonProtocol.valueToJson argument)])
  | .stack (items := items) _ children _ => fun ⟨child, invocation⟩ =>
      invocationToJson (children child) (target ++ [items.label child]) invocation
  | .field .. => fun invocation => Empty.elim invocation
  | .list .. => fun invocation => Empty.elim invocation
  | .sum .. => fun invocation => Empty.elim invocation
  | .computed .. => fun invocation => Empty.elim invocation
  | .text .. => fun invocation => Empty.elim invocation
  | .table .. => fun invocation => Empty.elim invocation
  | .visibleWhen .. => fun invocation => Empty.elim invocation
  | .disabledWhen .. => fun invocation => Empty.elim invocation
  | .button .. => fun invocation => Empty.elim invocation
  | .appendItemButton .. => fun invocation => Empty.elim invocation

private def invocationFromJson {ty : DataType} (component : Component ty)
    (target : List String) (json : Json) : Except String component.Invocation :=
  match component with
  | .actionWidget (value := value) (ids := ids) .. => do
      unless target.isEmpty do throw "Target continues beyond action widget"
      let name ← (← json.getObjVal? "action").getStr?
      let some action := (FinEnum.toList ids).find? (fun id => ids.label id == name)
        | throw s!"Unknown action: {name}"
      let fields ← json.getObj?
      match json.getObjVal? "argument" with
      | .ok argument =>
          if fields.size != 3 then throw "Expected only target, action and argument"
          return .editor action (← JsonProtocol.valueFromJson value argument)
      | .error _ =>
          if fields.size != 2 then throw "Expected only target and action"
          return .button action
  | .stack (items := items) _ children _ => do
      let name :: rest := target
        | throw "Missing widget target"
      let some child := (FinEnum.toList items).find? (fun child => items.label child == name)
        | throw s!"Unknown component: {name}"
      return ⟨child, ← invocationFromJson (children child) rest json⟩
  | .field .. => .error "Target is not an action widget"
  | .list .. => .error "Target is not an action widget"
  | .sum .. => .error "Target is not an action widget"
  | .computed .. => .error "Target is not an action widget"
  | .text .. => .error "Target is not an action widget"
  | .table .. => .error "Target is not an action widget"
  | .visibleWhen .. => .error "Target is not an action widget"
  | .disabledWhen .. => .error "Target is not an action widget"
  | .button .. => .error "Target is not an action widget"
  | .appendItemButton .. => .error "Target is not an action widget"

def encode {ty : DataType} {component : Component ty} (history : ComponentHistory component) : Json :=
  Json.mkObj [("value", JsonProtocol.valueToJson history.value),
    ("actions", toJson (history.actions.map (invocationToJson component [])))]

def verify {ty : DataType} (component : Component ty) (initial : ⟦ty⟧)
    (submission : Json) : Except String (ComponentHistory component) := do
  unless component.supportsHistory do throw "Component history is not supported yet"
  let fields ← submission.getObj?
  if fields.size != 2 then throw "Expected only value and actions in submission"
  let claimed ← JsonProtocol.valueFromJson ty (← submission.getObjVal? "value")
  let actions ← (← (← submission.getObjVal? "actions").getArr?).mapM fun json => do
    let target ← (← (← json.getObjVal? "target").getArr?).toList.mapM Json.getStr?
    invocationFromJson component target json
  let replayed ← (ComponentHistory.replay component initial actions).mapError toString
  if JsonProtocol.valueToJson replayed.value != JsonProtocol.valueToJson claimed then
    throw "Submitted value does not match action replay"
  return replayed

end Forms.Runtime.ComponentHistoryProtocol
