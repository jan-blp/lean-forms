import Forms.Core.Composition
import Lean.Data.Json

namespace Forms
open Lean Composition

variable {root input context t : DataType}

def DataType.toJson (t : DataType) : Json :=
  match t with
  | .list element => Json.mkObj [("kind", Lean.toJson "list"), ("element", element.toJson)]
  | .text => Json.mkObj [("kind", Lean.toJson "text")]
  | .boolean => Json.mkObj [("kind", Lean.toJson "boolean")]
  | .date => Json.mkObj [("kind", Lean.toJson "date")]
  | .natural => Json.mkObj [("kind", Lean.toJson "natural")]
  | .enum domain => Json.mkObj [("kind", Lean.toJson "enum"), ("options", Lean.toJson domain.options)]
  | .record fieldNames fieldTypes => Json.mkObj [("kind", Lean.toJson "record"),
      ("fields", Json.arr ((FinEnum.toList fieldNames).map fun i =>
        Json.mkObj [("name", Lean.toJson (fieldNames.label i)), ("type", DataType.toJson (fieldTypes i))]).toArray)]

namespace Runtime.JsonProtocol

def valueToJson {t} (value : ⟦t⟧) : Json :=
  match t with
  | .list element => Json.arr ((value.map (valueToJson (t := element))).toArray)
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .date => Lean.toJson (Date.toString value)
  | .natural => Lean.toJson (toString value)
  | .enum domain => Lean.toJson (FinEnum.equiv (α := domain) value).val
  | .record fieldNames fieldTypes => Json.mkObj ((FinEnum.toList fieldNames).map fun i =>
      (fieldNames.label i, valueToJson (t := fieldTypes i) (value i)))

private def sequenceFin {n : Nat} {α : Fin n → Type}
    (values : (i : Fin n) → Except String (α i)) : Except String ((i : Fin n) → α i) :=
  match n with
  | 0 => pure (fun i => Fin.elim0 i)
  | _ + 1 => do
    let head ← values 0
    let tail ← sequenceFin (fun i => values i.succ)
    pure (Fin.cons head tail)

private def sequence {ι : Type} [FinEnum ι] {α : ι → Type}
    (values : (i : ι) → Except String (α i)) : Except String ((i : ι) → α i) := do
  let result ← sequenceFin (fun i => values (FinEnum.equiv.symm i))
  pure fun i => (FinEnum.equiv.symm_apply_apply i) ▸ result (FinEnum.equiv i)

def valueFromJson (t : DataType) (json : Json) : Except String ⟦t⟧ :=
  match t with
  | .list element => do
    let items ← json.getArr?
    items.toList.mapM (valueFromJson element)
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
  | .record fieldNames fieldTypes => do
    let object ← json.getObj?
    if object.size != FinEnum.card fieldNames then
      throw "Wrong number of record fields in interpreter result"
    sequence (fun i => do valueFromJson (fieldTypes i) (← json.getObjVal? (fieldNames.label i)))

theorem valueFromJson_date_sound {json : Json} {date : Date}
    (h : valueFromJson .date json = .ok date) :
    valueToJson (t := .date) date = json := by
  cases json <;>
    simp_all [valueFromJson, Json.getStr?, bind, Except.bind, pure, Except.pure,
      valueToJson, toJson]
  split at h <;> simp_all
  grind [Date.ofString?_sound]

end Runtime.JsonProtocol

def Path.toList {source target : DataType} (path : Path source target) : List String :=
  match path with
  | .self => []
  | .field (fieldNames := fieldNames) fieldName rest => fieldNames.label fieldName :: Path.toList rest

def Expr.toJson {input t} (expression : Expr input t) : Json :=
  match expression with
  | .value v => Json.mkObj [("kind", Lean.toJson "value"), ("type", DataType.toJson t), ("value", Runtime.JsonProtocol.valueToJson v)]
  | .project p => Json.mkObj [("kind", Lean.toJson "project"), ("path", Lean.toJson (Path.toList p))]
  | .all items predicate => Json.mkObj [("kind", Lean.toJson "all"),
      ("items", items.toJson), ("predicate", predicate.toJson)]
  | .and l r => binary "and" (Expr.toJson l) (Expr.toJson r)
  | .dateLe l r => binary "dateLe" (Expr.toJson l) (Expr.toJson r)
  | .natLe l r => binary "natLe" (Expr.toJson l) (Expr.toJson r)
where
  binary (kind : String) (left right : Json) : Json :=
    Json.mkObj [("kind", Lean.toJson kind), ("left", left), ("right", right)]

def Widget.name (widget : Widget t) : String :=
  match widget with
  | .textInput => "textInput"
  | .checkbox => "checkbox"
  | .dateInput => "dateInput"
  | .naturalInput => "naturalInput"
  | .select => "select"

def Component.toJson {state : DataType} (component : Component state) : Json :=
  match component with
  | .field (value := value) path label widget => Json.mkObj [
      ("kind", Lean.toJson "field"), ("path", Lean.toJson (Path.toList path)),
      ("schema", DataType.toJson value), ("label", Lean.toJson label), ("widget", Lean.toJson (Widget.name widget))]
  | .list (element := element) path label item defaultItem => Json.mkObj [
      ("kind", Lean.toJson "list"), ("path", Lean.toJson (Path.toList path)),
      ("schema", DataType.toJson (.list element)), ("label", Lean.toJson label),
      ("item", Component.toJson item), ("defaultItem", Runtime.JsonProtocol.valueToJson defaultItem)]
  | .visibleWhen condition body => Json.mkObj [
      ("kind", Lean.toJson "visibleWhen"), ("condition", Expr.toJson condition), ("body", Component.toJson body)]
  | .stack (items := items) label children => Json.mkObj [
      ("kind", Lean.toJson "stack"), ("label", Lean.toJson label),
      ("children", Lean.toJson ((FinEnum.toList items).map fun index => Component.toJson (children index)))]

namespace Runtime.JsonProtocol

def encode {context : DataType} (form : Component context) (value : ⟦context⟧) : String :=
  (Json.mkObj [("version", Lean.toJson (4 : Nat)), ("schema", DataType.toJson context),
    ("form", Component.toJson form), ("value", valueToJson value)]).compress

end Runtime.JsonProtocol

end Forms
