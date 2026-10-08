import Forms.Domain.Model
import Lean.Data.Json

namespace Forms.Technology.Specification
open Lean

def typeToJson : Ty → Json
  | .text => Json.mkObj [("kind", toJson "text")]
  | .boolean => Json.mkObj [("kind", toJson "boolean")]
  | .natural => Json.mkObj [("kind", toJson "natural")]
  | .pair l r => Json.mkObj [("kind", toJson "pair"), ("left", typeToJson l), ("right", typeToJson r)]

-- Decimal strings preserve Lean's unbounded naturals across the JSON boundary.
def valueToJson {type : Ty} (value : Ty.denote type) : Json :=
  match type with
  | .text => toJson value
  | .boolean => toJson value
  | .natural => toJson (toString value)
  | .pair l r => Json.arr #[valueToJson (type := l) value.1, valueToJson (type := r) value.2]

def valueFromJson (type : Ty) (json : Json) : Except String (Ty.denote type) :=
  match type with
  | .text => json.getStr?
  | .boolean => json.getBool?
  | .natural => do
    let text ← json.getStr?
    match text.toNat? with
    | some n => pure n
    | none => throw "Invalid natural in interpreter result"
  | .pair l r => do
    let items ← json.getArr?
    if items.size != 2 then throw "Expected a pair in interpreter result"
    return (← valueFromJson l items[0]!, ← valueFromJson r items[1]!)

def pathToList {root target : Ty} : Path root target → List Nat
  | .here => []
  | .left rest => 0 :: pathToList rest
  | .right rest => 1 :: pathToList rest

def exprToJson {root type : Ty} : Expr root type → Json
  | .value v => Json.mkObj [("kind", toJson "value"), ("type", typeToJson type), ("value", valueToJson v)]
  | .project p => Json.mkObj [("kind", toJson "project"), ("path", toJson (pathToList p))]
  | .not e => Json.mkObj [("kind", toJson "not"), ("operand", exprToJson e)]
  | .and l r => binary "and" (exprToJson l) (exprToJson r)
  | .textEquals l r => binary "textEquals" (exprToJson l) (exprToJson r)
  | .natLe l r => binary "natLe" (exprToJson l) (exprToJson r)
where
  binary (kind : String) (left right : Json) : Json :=
    Json.mkObj [("kind", toJson kind), ("left", left), ("right", right)]

def controlName {type : Ty} : Control type → String
  | .text => "text"
  | .checkbox => "checkbox"
  | .natural => "natural"

def formToJson {root type : Ty} : Form root type → Json
  | .field label control => Json.mkObj [("kind", toJson "field"), ("label", toJson label),
      ("control", toJson (controlName control))]
  | .group label l r => Json.mkObj [("kind", toJson "group"), ("label", toJson label),
      ("left", formToJson l), ("right", formToJson r)]
  | .visibleWhen condition body => Json.mkObj [("kind", toJson "visibleWhen"),
      ("condition", exprToJson condition), ("body", formToJson body)]

def encode {root : Ty} (form : Form root root) (value : Ty.denote root) : String :=
  (Json.mkObj [("version", toJson (1 : Nat)), ("schema", typeToJson root),
    ("form", formToJson form), ("value", valueToJson value)]).compress

end Forms.Technology.Specification
