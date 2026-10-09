import Forms.Core.Form
import Lean.Data.Json

namespace Forms
open Lean

def DataType.toJson (t : DataType) : Json :=
  match t with
  | .text => Json.mkObj [("kind", Lean.toJson "text")]
  | .boolean => Json.mkObj [("kind", Lean.toJson "boolean")]
  | .date => Json.mkObj [("kind", Lean.toJson "date")]
  | .natural => Json.mkObj [("kind", Lean.toJson "natural")]
  | .enum domain => Json.mkObj [("kind", Lean.toJson "enum"), ("options", Lean.toJson domain.options)]

namespace Runtime.JsonProtocol

def valueToJson {type : DataType} (value : ⟦type⟧) : Json :=
  match type with
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .date => Lean.toJson (Date.toString value)
  | .natural => Lean.toJson (toString value)
  | .enum domain => Lean.toJson (FinEnum.equiv (α := domain) value).val

def valueFromJson (type : DataType) (json : Json) : Except String ⟦type⟧ :=
  match type with
  | .text => json.getStr?
  | .boolean => json.getBool?
  | .date => do
    let text ← json.getStr?
    match Date.ofString? text with
    | some date => pure date
    | none => throw "Expected a valid date in YYYY-MM-DD format (0001–9999)"
  | .natural => do
    let text ← json.getStr?
    match text.toNat? with
    | some n => pure n
    | none => throw "Invalid natural in interpreter result"
  | .enum domain => do
    let index ← json.getNat?
    if h : index < FinEnum.card domain then return FinEnum.equiv.symm ⟨index, h⟩
    else throw "Invalid enum in interpreter result"

theorem valueFromJson_date_sound {json : Json} {date : Date}
    (h : valueFromJson .date json = .ok date) :
    valueToJson (type := .date) date = json := by
  cases json <;>
    simp_all [valueFromJson, Json.getStr?, bind, Except.bind, pure, Except.pure,
      valueToJson, toJson]
  split at h <;> simp_all
  grind [Date.ofString?_sound]

end Runtime.JsonProtocol

def Path.toList {source target : DataType} (path : Path source target) : List Nat :=
  match path with
  | .self => []

def Expr.toJson {input type : DataType} (expression : Expr input type) : Json :=
  match expression with
  | .value v => Json.mkObj [("kind", Lean.toJson "value"), ("type", DataType.toJson type), ("value", Runtime.JsonProtocol.valueToJson v)]
  | .project p => Json.mkObj [("kind", Lean.toJson "project"), ("path", Lean.toJson (Path.toList p))]
  | .and l r => binary "and" (Expr.toJson l) (Expr.toJson r)
  | .dateLe l r => binary "dateLe" (Expr.toJson l) (Expr.toJson r)
  | .natLe l r => binary "natLe" (Expr.toJson l) (Expr.toJson r)
where
  binary (kind : String) (left right : Json) : Json :=
    Json.mkObj [("kind", Lean.toJson kind), ("left", left), ("right", right)]

def Widget.name {type : DataType} (widget : Widget type) : String :=
  match widget with
  | .textInput => "textInput"
  | .checkbox => "checkbox"
  | .dateInput => "dateInput"
  | .naturalInput => "naturalInput"
  | .select => "select"

def Form.toJson {type : DataType} (form : Form type) : Json :=
  match form with
  | .field label widget => Json.mkObj [("kind", Lean.toJson "field"), ("label", Lean.toJson label),
      ("widget", Lean.toJson (Widget.name widget))]

namespace Runtime.JsonProtocol

def encode {context : DataType} (form : Form context) (value : ⟦context⟧) : String :=
  (Json.mkObj [("version", Lean.toJson (1 : Nat)), ("schema", DataType.toJson context),
    ("form", Form.toJson form), ("value", valueToJson value)]).compress

end Runtime.JsonProtocol

end Forms
