module

public import Forms.Runtime.Identity
public import Lean.Data.Json

@[expose] public section

namespace Forms.Runtime.ControlKeyProtocol
open Lean

def stepToJson : Feedback.Step → Json
  | .field name => toJson name
  | .constructor tag => Json.mkObj [("constructor", toJson tag)]
  | .index position => toJson position

def stepFromJson : Json → Except String Feedback.Step
  | .str name => .ok (.field name)
  | .num number => .index <$> fromJson? (.num number)
  | json => .constructor <$> json.getObjValAs? String "constructor"

def toString (key : ControlKey) : String :=
  let json := match key with
    | .edit location => Json.arr (#[toJson ("edit" : String)] ++ (location.map stepToJson).toArray)
    | .select location => Json.arr (#[toJson ("select" : String)] ++ (location.map stepToJson).toArray)
    | .add location => Json.arr (#[toJson ("add" : String)] ++ (location.map stepToJson).toArray)
    | .remove location => Json.arr (#[toJson ("remove" : String)] ++ (location.map stepToJson).toArray)
    | .selectRow scope row => Json.arr (#[toJson ("selectRow" : String)] ++ (scope ++ [row]).toArray.map toJson)
    | .press route location => Json.arr #[toJson ("press" : String), toJson route,
        Json.arr (location.map stepToJson).toArray]
  json.compress

def fromJson (json : Json) : Except String ControlKey := do
  match (← json.getArr?).toList with
  | .str "edit" :: steps => .edit <$> steps.mapM stepFromJson
  | .str "select" :: steps => .select <$> steps.mapM stepFromJson
  | .str "add" :: steps => .add <$> steps.mapM stepFromJson
  | .str "remove" :: steps => .remove <$> steps.mapM stepFromJson
  | .str "selectRow" :: positions =>
    match (← positions.mapM (fromJson? (α := Nat))).reverse with
    | row :: scope => pure (.selectRow scope.reverse row)
    | [] => throw "Expected a row index."
  | [.str "press", route, location] =>
    pure (.press (← fromJson? route) (← (← location.getArr?).toList.mapM stepFromJson))
  | _ => throw "Unknown action or invalid key shape."

def fromString (key : String) : Except String ControlKey :=
  (Json.parse key >>= fromJson).mapError (s!"Invalid control key: {·}")

end Forms.Runtime.ControlKeyProtocol
