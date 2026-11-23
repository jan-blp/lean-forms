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
    | _ => .error "Expected a list of texts."
  | json@(.obj _) => do
    let evidence ← json.getObjVal? "pick"
    .pick <$> fromJson? evidence
  | .null
  | .num _ => .error "Expected a text, boolean, list of texts or pick."

def argumentFromJson : Option Json → Except String (Option Input)
  | none => .ok none
  | some value => some <$> fromJson value

end Forms.Runtime.InputProtocol
