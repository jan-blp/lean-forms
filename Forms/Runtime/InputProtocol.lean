module

public import Forms.Runtime.Input
public import Lean.Data.Json

@[expose] public section

namespace Forms.Runtime.InputProtocol
open Lean

def fromJson : Json → Except String Input
  | .str value => .ok (.text value)
  | .bool value => .ok (.boolean value)
  | .arr values => .texts <$> values.toList.mapM fun
    | .str value => .ok value
    | .null
    | .bool _
    | .num _
    | .arr _
    | .obj _ => .error "Expected a list of texts."
  | json@(.obj _) =>
    if let .ok evidence := json.getObjVal? "pick" then .pick <$> fromJson? evidence
    else if let .ok input := json.getObjVal? "lookup" then .lookup <$> fromJson? input
    else .error "Expected a pick or lookup command."
  | .null
  | .num _ => .error "Expected a text, boolean, list of texts, pick or lookup command."

def argumentFromJson : Option Json → Except String (Option Input)
  | none => .ok none
  | some value => some <$> fromJson value

end Forms.Runtime.InputProtocol
