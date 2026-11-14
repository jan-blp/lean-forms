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
    | .press route location => Json.arr #[toJson ("press" : String), toJson route,
        Json.arr (location.map stepToJson).toArray]
    | .tab route location => Json.arr #[toJson ("tab" : String), toJson route,
        Json.arr (location.map stepToJson).toArray]
  json.compress

def fromJson (json : Json) : Except String ControlKey := do
  match (← json.getArr?).toList with
  | .str "edit" :: steps => .edit <$> steps.mapM stepFromJson
  | .str "select" :: steps => .select <$> steps.mapM stepFromJson
  | [.str "press", route, location] =>
    pure (.press (← fromJson? route) (← (← location.getArr?).toList.mapM stepFromJson))
  | [.str "tab", route, location] =>
    pure (.tab (← fromJson? route) (← (← location.getArr?).toList.mapM stepFromJson))
  | _ => throw "Unknown action or invalid key shape."

def fromString (key : String) : Except String ControlKey :=
  (Json.parse key >>= fromJson).mapError (s!"Invalid control key: {·}")

end Forms.Runtime.ControlKeyProtocol
