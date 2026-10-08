import Forms.Core.Form
import Lean.Data.Json

namespace Forms
open Lean

def DataType.toJson (t : DataType) : Json :=
  match t with
  | .text => Json.mkObj [("kind", Lean.toJson "text")]
  | .boolean => Json.mkObj [("kind", Lean.toJson "boolean")]
  | .natural => Json.mkObj [("kind", Lean.toJson "natural")]

namespace Runtime.JsonProtocol

def valueToJson {type : DataType} (value : DataType.denote type) : Json :=
  match type with
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson (toString value)

def valueFromJson (type : DataType) (json : Json) : Except String (DataType.denote type) :=
  match type with
  | .text => json.getStr?
  | .boolean => json.getBool?
  | .natural => do
    let text ← json.getStr?
    match text.toNat? with
    | some n => pure n
    | none => throw "Invalid natural in interpreter result"

end Runtime.JsonProtocol

def Path.toList {root target : DataType} (path : Path root target) : List Nat :=
  match path with
  | .self => []

def Expr.toJson {root type : DataType} (expression : Expr root type) : Json :=
  match expression with
  | .value v => Json.mkObj [("kind", Lean.toJson "value"), ("type", DataType.toJson type), ("value", Runtime.JsonProtocol.valueToJson v)]
  | .project p => Json.mkObj [("kind", Lean.toJson "project"), ("path", Lean.toJson (Path.toList p))]
  | .and l r => binary "and" (Expr.toJson l) (Expr.toJson r)
  | .natLe l r => binary "natLe" (Expr.toJson l) (Expr.toJson r)
where
  binary (kind : String) (left right : Json) : Json :=
    Json.mkObj [("kind", Lean.toJson kind), ("left", left), ("right", right)]

def Widget.name {type : DataType} (widget : Widget type) : String :=
  match widget with
  | .textInput => "textInput"
  | .checkbox => "checkbox"
  | .naturalInput => "naturalInput"

def Form.toJson {root type : DataType} (form : Form root type) : Json :=
  match form with
  | .field label widget => Json.mkObj [("kind", Lean.toJson "field"), ("label", Lean.toJson label),
      ("widget", Lean.toJson (Widget.name widget))]

namespace Runtime.JsonProtocol

def encode {root : DataType} (form : Form root root) (value : DataType.denote root) : String :=
  (Json.mkObj [("version", Lean.toJson (1 : Nat)), ("schema", DataType.toJson root),
    ("form", Form.toJson form), ("value", valueToJson value)]).compress

end Runtime.JsonProtocol

end Forms
