import Forms.Core.ComponentHistory
import Forms.Runtime.JsonProtocol

namespace Forms.Runtime.ComponentHistoryProtocol
open Lean Composition

inductive Error where
  | malformedJson (message : String)
  | invalidFields (expected : List String)
  | invalidValue (message : String)
  | invalidArgument (message : String)
  | missingArgument
  | unexpectedArgument
  | unknownAction (name : String)
  | unknownComponent (name : String)
  | missingTarget
  | targetBeyondWidget
  | targetNotWidget
  | unsupportedComponent
  | invocation (error : Component.InvocationError)
  | valueMismatch
  deriving DecidableEq, BEq, Repr

instance : ToString Error where
  toString
    | .malformedJson message => message
    | .invalidFields expected => "Expected only " ++ String.intercalate ", " expected
    | .invalidValue message => s!"Invalid submitted value: {message}"
    | .invalidArgument message => s!"Invalid action argument: {message}"
    | .missingArgument => "Action requires an editor argument"
    | .unexpectedArgument => "Button does not accept an argument"
    | .unknownAction name => s!"Unknown action: {name}"
    | .unknownComponent name => s!"Unknown component: {name}"
    | .missingTarget => "Missing widget target"
    | .targetBeyondWidget => "Target continues beyond action widget"
    | .targetNotWidget => "Target is not an action widget"
    | .unsupportedComponent => "Component history is not supported yet"
    | .invocation error => toString error
    | .valueMismatch => "Submitted value does not match action replay"

private def readJson {α : Type} (result : Except String α) : Except Error α :=
  result.mapError Error.malformedJson

private def argumentToJson {ty : DataType}
  (presentation : Action.Presentation ty)
  : presentation.Argument → List (String × Json) :=
  match presentation with
  | .button .. => fun () => []
  | .editor .. => fun argument => [("argument", JsonProtocol.valueToJson argument)]

private def argumentFromJson {ty : DataType}
  (presentation : Action.Presentation ty)
  (json : Json)
  : Except Error presentation.Argument :=
  match presentation with
  | .button .. => do
      let fields ← readJson json.getObj?
      if (json.getObjVal? "argument").isOk then throw .unexpectedArgument
      if fields.size != 2 then throw (.invalidFields ["target", "action"])
      return ()
  | .editor .. => do
      let fields ← readJson json.getObj?
      let argument ← (json.getObjVal? "argument").mapError (fun _ => Error.missingArgument)
      if fields.size != 3 then throw (.invalidFields ["target", "action", "argument"])
      (JsonProtocol.valueFromJson ty argument).mapError Error.invalidArgument

private def invocationToJson {ty : DataType}
  (component : Component ty)
  (target : List String)
  : component.Invocation → Json :=
  match component with
  | .actionWidget (ids := ids) _ _ actions => fun invocation =>
      Json.mkObj ([("target", toJson target), ("action", toJson (ids.label invocation.name))] ++
        argumentToJson (actions invocation.name).presentation invocation.argument)
  | .stack (items := items) _ children _ => fun ⟨child, invocation⟩ =>
      invocationToJson (children child) (target ++ [items.label child]) invocation
  | .field .. => fun invocation => Empty.elim invocation
  | .list .. => fun invocation => Empty.elim invocation
  | .sum .. => fun invocation => Empty.elim invocation
  | .computed .. => fun invocation => Empty.elim invocation
  | .text .. => fun invocation => Empty.elim invocation
  | .table .. => fun invocation => Empty.elim invocation
  | .visibleWhen _ body => invocationToJson body target
  | .disabledWhen _ body => invocationToJson body target
  | .button .. => fun invocation => Empty.elim invocation
  | .appendItemButton .. => fun invocation => Empty.elim invocation

private def invocationFromJson {ty : DataType}
  (component : Component ty)
  (target : List String)
  (json : Json)
  : Except Error component.Invocation :=
  match component with
  | .actionWidget (ids := ids) _ _ actions => do
      unless target.isEmpty do throw .targetBeyondWidget
      let name ← readJson ((json.getObjVal? "action") >>= Json.getStr?)
      let some action := (FinEnum.toList ids).find? (fun id => ids.label id == name)
        | throw (.unknownAction name)
      return ⟨action, ← argumentFromJson (actions action).presentation json⟩
  | .stack (items := items) _ children _ => do
      let name :: rest := target
        | throw .missingTarget
      let some child := (FinEnum.toList items).find? (fun child => items.label child == name)
        | throw (.unknownComponent name)
      return ⟨child, ← invocationFromJson (children child) rest json⟩
  | .field .. => .error .targetNotWidget
  | .list .. => .error .targetNotWidget
  | .sum .. => .error .targetNotWidget
  | .computed .. => .error .targetNotWidget
  | .text .. => .error .targetNotWidget
  | .table .. => .error .targetNotWidget
  | .visibleWhen _ body => invocationFromJson body target json
  | .disabledWhen _ body => invocationFromJson body target json
  | .button .. => .error .targetNotWidget
  | .appendItemButton .. => .error .targetNotWidget

def encode {ty : DataType} {component : Component ty}
  (history : ComponentHistory component)
  : Json :=
  Json.mkObj [("value", JsonProtocol.valueToJson history.value),
    ("actions", toJson (history.actions.map (invocationToJson component [])))]

def verify {ty : DataType}
  (component : Component ty)
  (initial : ⟦ty⟧)
  (submission : Json)
  : Except Error (ComponentHistory component) := do
  unless component.supportsHistory do throw .unsupportedComponent
  let fields ← readJson submission.getObj?
  if fields.size != 2 then throw (.invalidFields ["value", "actions"])
  let value ← readJson (submission.getObjVal? "value")
  let claimed ← (JsonProtocol.valueFromJson ty value).mapError Error.invalidValue
  let entries ← readJson ((submission.getObjVal? "actions") >>= Json.getArr?)
  let actions ← entries.mapM fun json => do
    let segments ← readJson ((json.getObjVal? "target") >>= Json.getArr?)
    let target ← readJson (segments.toList.mapM Json.getStr?)
    invocationFromJson component target json
  let replayed ← (ComponentHistory.replay component initial actions).mapError Error.invocation
  if JsonProtocol.valueToJson replayed.value != JsonProtocol.valueToJson claimed then
    throw .valueMismatch
  return replayed

end Forms.Runtime.ComponentHistoryProtocol
