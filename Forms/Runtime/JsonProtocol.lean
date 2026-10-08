import Forms.Core.Form
import Lean.Data.Json

namespace Forms
open Lean

def DataType.toJson (t : DataType) : Json :=
  match t with
  | .text => Json.mkObj [("kind", Lean.toJson "text")]
  | .boolean => Json.mkObj [("kind", Lean.toJson "boolean")]
  | .natural => Json.mkObj [("kind", Lean.toJson "natural")]
  | .record fields children => Json.mkObj [("kind", Lean.toJson "record"),
      ("fields", Json.arr ((FinEnum.toList fields.type).map fun i =>
        Json.mkObj [("name", Lean.toJson (fields.label i)), ("type", DataType.toJson (children i))]).toArray)]

namespace Runtime.JsonProtocol

def valueToJson {type : DataType} (value : DataType.denote type) : Json :=
  match type with
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson (toString value)
  | .record fields children => Json.mkObj ((FinEnum.toList fields.type).map fun i =>
      (fields.label i, valueToJson (type := children i) (value i)))

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

def valueFromJson (type : DataType) (json : Json) : Except String (DataType.denote type) :=
  match type with
  | .text => json.getStr?
  | .boolean => json.getBool?
  | .natural => do
    let text ← json.getStr?
    match text.toNat? with
    | some n => pure n
    | none => throw "Invalid natural in interpreter result"
  | .record fields children => do
    let object ← json.getObj?
    if object.size != FinEnum.card fields.type then
      throw "Wrong number of record fields in interpreter result"
    sequence (fun i => do valueFromJson (children i) (← json.getObjVal? (fields.label i)))

end Runtime.JsonProtocol

def Path.toList {root target : DataType} (path : Path root target) : List String :=
  match path with
  | .self => []
  | .child (fields := fields) index rest => fields.label index :: Path.toList rest

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
  | .group (fields := fields) label children => Json.mkObj [("kind", Lean.toJson "group"), ("label", Lean.toJson label),
      ("children", Json.mkObj ((FinEnum.toList fields.type).map fun i => (fields.label i, Form.toJson (children i))))]

namespace Runtime.JsonProtocol

def encode {root : DataType} (form : Form root root) (value : DataType.denote root) : String :=
  (Json.mkObj [("version", Lean.toJson (1 : Nat)), ("schema", DataType.toJson root),
    ("form", Form.toJson form), ("value", valueToJson value)]).compress

end Runtime.JsonProtocol

end Forms
