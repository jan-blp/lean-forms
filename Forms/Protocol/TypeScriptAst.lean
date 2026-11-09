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
  /-- A type declared in the module for Lean namespace `path`. -/
  | reference (path : List String) (name : String)
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

/-- The types of Lean namespace `path`, generated as `path/….ts`. -/
structure Module where
  path : List String
  declarations : List TypeAlias
  deriving BEq, Repr, Lean.ToExpr

structure Program where
  modules : List Module
  deriving BEq, Repr, Lean.ToExpr

private def quoted (text : String) : String := (Lean.Json.str text).compress

/-- The name a module is imported under. -/
def alias (path : List String) : String := path.getLast?.getD ""

mutual
private def renderType (current : List String) : TS.Type → String
  | .string => "string"
  | .boolean => "boolean"
  | .number => "number"
  | .unknown => "unknown"
  | .null => "null"
  | .stringLiteral value => quoted value
  | .reference path name => if path == current then name else alias path ++ "." ++ name
  | .array element =>
    let text := renderType current element
    (match element with | .union .. => "(" ++ text ++ ")" | _ => text) ++ "[]"
  | .tuple elements => "[" ++ String.intercalate ", " (elements.map (renderType current)) ++ "]"
  | .union first second rest =>
    String.intercalate " | " (renderType current first :: renderType current second :: rest.map (renderType current))
  | .object properties => "{ " ++ String.intercalate "; " (properties.map (renderProperty current)) ++ " }"

private def renderProperty (current : List String) : Property → String
  | .mk name type optional => quoted name ++ (if optional then "?" else "") ++ ": " ++ renderType current type
end

mutual
private def typePaths : TS.Type → List (List String)
  | .reference path _ => [path]
  | .array element => typePaths element
  | .tuple elements => elements.flatMap typePaths
  | .union first second rest => typePaths first ++ typePaths second ++ rest.flatMap typePaths
  | .object properties => properties.flatMap propertyPaths
  | _ => []

private def propertyPaths : Property → List (List String)
  | .mk _ type _ => typePaths type
end

/-- Renders `type` as seen from the module for namespace `current`. -/
def Type.pretty (type : TS.Type) (current : List String := []) : String := renderType current type

def Module.file (module : Module) : String := String.intercalate "/" module.path ++ ".ts"

/-- The other modules this module references. -/
def Module.imports (module : Module) : List (List String) :=
  (module.declarations.flatMap (typePaths ·.type)).eraseDups.filter (· != module.path)

/-- The import specifier for module `target`, relative to module `source`. -/
def relativeImport (source target : List String) : String :=
  let directory := source.dropLast
  let common := ((directory.zip target.dropLast).takeWhile fun (a, b) => a == b).length
  let up := directory.length - common
  let prefix_ := if up == 0 then "./" else String.join (List.replicate up "../")
  prefix_ ++ String.intercalate "/" (target.drop common) ++ ".js"

def Module.pretty (module : Module) : String :=
  let imports := module.imports.map fun path =>
    "import type * as " ++ alias path ++ " from " ++ quoted (relativeImport module.path path) ++ ";\n"
  String.join imports ++ (if imports.isEmpty then "" else "\n") ++
    String.join (module.declarations.map fun decl =>
      "export type " ++ decl.name ++ " = " ++ decl.type.pretty module.path ++ ";\n")

end Forms.Protocol.TS
