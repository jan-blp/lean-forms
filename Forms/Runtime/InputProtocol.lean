module

public import Forms.Runtime.Input
public import Lean

@[expose] public section

namespace Forms.Runtime.InputProtocol
open Lean

def fromJson : Json → Except String Input
  | .str value => .ok (.text value)
  | .bool value => .ok (.boolean value)
  | value@(.num _) => Input.index <$> value.getNat?
  | _ => .error "Expected a text, boolean, or index argument."

def argumentFromJson : Option Json → Except String (Option Input)
  | none => .ok none
  | some value => some <$> fromJson value

end Forms.Runtime.InputProtocol
