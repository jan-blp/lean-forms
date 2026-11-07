module

public import Lean.Data.Json
public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

public section
namespace Forms.Protocol.TS

mutual
inductive «Type» where
  | string
  | boolean
  | number
  | unknown
  | null
  | stringLiteral (value : String)
  | reference (name : String)
  | array (element : TS.Type)
  | tuple (elements : List TS.Type)
  | union (first second : TS.Type) (rest : List TS.Type)
  | object (properties : List Property)
  deriving BEq, Repr, Lean.ToExpr

inductive Property where
  | mk (name : String) (type : TS.Type) (optional : Bool := false)
  deriving BEq, Repr, Lean.ToExpr
end

structure TypeAlias where
  name : String
  type : TS.Type
  deriving BEq, Repr, Lean.ToExpr

structure Module where
  declarations : List TypeAlias
  deriving BEq, Repr, Lean.ToExpr

private def quoted (text : String) : String := (Lean.Json.str text).compress

mutual
private def renderType : TS.Type → String
  | .string => "string"
  | .boolean => "boolean"
  | .number => "number"
  | .unknown => "unknown"
  | .null => "null"
  | .stringLiteral value => quoted value
  | .reference name => name
  | .array element =>
    let text := renderType element
    (match element with | .union .. => "(" ++ text ++ ")" | _ => text) ++ "[]"
  | .tuple elements => "[" ++ String.intercalate ", " (elements.map renderType) ++ "]"
  | .union first second rest => String.intercalate " | " (renderType first :: renderType second :: rest.map renderType)
  | .object properties => "{ " ++ String.intercalate "; " (properties.map renderProperty) ++ " }"

private def renderProperty : Property → String
  | .mk name type optional => quoted name ++ (if optional then "?" else "") ++ ": " ++ renderType type
end

def Type.pretty (type : TS.Type) : String := renderType type

def Module.pretty (module : Module) : String :=
  String.join (module.declarations.map fun decl =>
    "export type " ++ decl.name ++ " = " ++ decl.type.pretty ++ ";\n")

end Forms.Protocol.TS
