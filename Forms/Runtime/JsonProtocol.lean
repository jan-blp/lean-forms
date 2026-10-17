import Forms.Core.Form
import Forms.Core.RefinedDataType
import Lean.Data.Json

namespace Forms
open Lean

variable {root t target : DataType}

def DataType.toJson (t : DataType) : Json :=
  match t with
  | .sum tags constructors => Json.mkObj [("kind", Lean.toJson "sum"),
      ("constructors", Json.arr ((FinEnum.toList tags.type).map fun i =>
        Json.mkObj [("name", Lean.toJson (tags.label i)), ("type", DataType.toJson (constructors i))]).toArray)]
  | .list element => Json.mkObj [("kind", Lean.toJson "list"), ("element", DataType.toJson element)]
  | .text => Json.mkObj [("kind", Lean.toJson "text")]
  | .boolean => Json.mkObj [("kind", Lean.toJson "boolean")]
  | .natural => Json.mkObj [("kind", Lean.toJson "natural")]
  | .enum domain => Json.mkObj [("kind", Lean.toJson "enum"), ("options", Lean.toJson (Enum.options domain))]
  | .record fields children => Json.mkObj [("kind", Lean.toJson "record"),
      ("fields", Json.arr ((FinEnum.toList fields.type).map fun i =>
        Json.mkObj [("name", Lean.toJson (fields.label i)), ("type", DataType.toJson (children i))]).toArray)]

namespace Runtime.JsonProtocol

def valueToJson {t} (value : DataType.denote t) : Json :=
  match t with
  | .sum tags constructors => Json.mkObj [("tag", Lean.toJson (tags.label value.tag)),
      ("value", valueToJson (t := constructors value.tag) value.payload)]
  | .list element => Json.arr ((value.map (valueToJson (t := element))).toArray)
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson (toString value)
  | .enum domain => Lean.toJson (FinEnum.equiv (α := domain.type) value).val
  | .record fields children => Json.mkObj ((FinEnum.toList fields.type).map fun i =>
      (fields.label i, valueToJson (t := children i) (value i)))

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

def valueFromJson (t : DataType) (json : Json) : Except String (DataType.denote t) :=
  match t with
  | .sum tags constructors => do
    let fields ← json.getObj?
    if fields.size != 2 then throw "Expected only tag and value in sum"
    let name ← (← json.getObjVal? "tag").getStr?
    let some tag := (FinEnum.toList tags.type).find? (fun i => tags.label i == name)
      | throw "Invalid sum tag in interpreter result"
    let payload ← valueFromJson (constructors tag) (← json.getObjVal? "value")
    return ⟨tag, payload⟩
  | .list element => do
    let items ← json.getArr?
    items.toList.mapM (valueFromJson element)
  | .text => json.getStr?
  | .boolean => json.getBool?
  | .natural => do
    let text ← json.getStr?
    match text.toNat? with
    | some n => pure n
    | none => throw "Invalid natural in interpreter result"
  | .enum domain => do
    let index ← json.getNat?
    if h : index < FinEnum.card domain.type then return FinEnum.equiv.symm ⟨index, h⟩
    else throw "Invalid enum in interpreter result"
  | .record fields children => do
    let object ← json.getObj?
    if object.size != FinEnum.card fields.type then
      throw "Wrong number of record fields in interpreter result"
    sequence (fun i => do valueFromJson (children i) (← json.getObjVal? (fields.label i)))

end Runtime.JsonProtocol

def Path.toList {root target} (path : Path root target) : List String :=
  match path with
  | .self => []
  | .child (fields := fields) index rest => fields.label index :: Path.toList rest

def Expr.toJson {root t} (expression : Expr root t) : Json :=
  match expression with
  | .value v => Json.mkObj [("kind", Lean.toJson "value"), ("type", DataType.toJson t), ("value", Runtime.JsonProtocol.valueToJson v)]
  | .project p => Json.mkObj [("kind", Lean.toJson "project"), ("path", Lean.toJson (Path.toList p))]
  | .all items predicate => Json.mkObj [("kind", Lean.toJson "all"),
      ("items", Expr.toJson items), ("predicate", Expr.toJson predicate)]
  | .cases (tags := tags) subject branches => Json.mkObj [("kind", Lean.toJson "cases"),
      ("type", DataType.toJson t), ("subject", Expr.toJson subject),
      ("branches", Json.mkObj ((FinEnum.toList tags.type).map fun i => (tags.label i, Expr.toJson (branches i))))]
  | .sum items expression => Json.mkObj [("kind", Lean.toJson "sum"),
      ("items", Expr.toJson items), ("expression", Expr.toJson expression)]
  | .natMul l r => binary "natMul" (Expr.toJson l) (Expr.toJson r)
  | .not operand => Json.mkObj [("kind", Lean.toJson "not"), ("operand", Expr.toJson operand)]
  | .and l r => binary "and" (Expr.toJson l) (Expr.toJson r)
  | .natLe l r => binary "natLe" (Expr.toJson l) (Expr.toJson r)
where
  binary (kind : String) (left right : Json) : Json :=
    Json.mkObj [("kind", Lean.toJson kind), ("left", left), ("right", right)]

def Widget.name (widget : Widget t) : String :=
  match widget with
  | .textInput => "textInput"
  | .checkbox => "checkbox"
  | .naturalInput => "naturalInput"
  | .select => "select"

def Form.toJson {root t} (form : Form root t) : Json :=
  match form with
  | .sum (tags := tags) label branches defaults => Json.mkObj [("kind", Lean.toJson "sum"),
      ("label", Lean.toJson label),
      ("branches", Json.mkObj ((FinEnum.toList tags.type).map fun i => (tags.label i, Form.toJson (branches i)))),
      ("defaults", Json.mkObj ((FinEnum.toList tags.type).map fun i => (tags.label i, Runtime.JsonProtocol.valueToJson (defaults i))))]
  | .list label item defaultItem => Json.mkObj [("kind", Lean.toJson "list"),
      ("label", Lean.toJson label), ("item", Form.toJson item),
      ("defaultItem", Runtime.JsonProtocol.valueToJson defaultItem)]
  | .field label widget => Json.mkObj [("kind", Lean.toJson "field"), ("label", Lean.toJson label),
      ("widget", Lean.toJson (Widget.name widget))]
  | .group (fields := fields) label children displayOrder => Json.mkObj [("kind", Lean.toJson "group"), ("label", Lean.toJson label),
      ("children", Json.mkObj ((FinEnum.toList fields.type).map fun i => (fields.label i, Form.toJson (children i)))),
      ("displayOrder", Lean.toJson ((FinEnum.toList fields.type).map fun i => fields.label (displayOrder i)))]
  | .computed (result := result) label expression body => Json.mkObj [("kind", Lean.toJson "computed"),
      ("label", Lean.toJson label), ("type", DataType.toJson result),
      ("expression", Expr.toJson expression), ("body", Form.toJson body)]
  | .visibleWhen condition body => Json.mkObj [("kind", Lean.toJson "visibleWhen"),
      ("condition", Expr.toJson condition), ("body", Form.toJson body)]
  | .disabledWhen condition body => Json.mkObj [("kind", Lean.toJson "disabledWhen"),
      ("condition", Expr.toJson condition), ("body", Form.toJson body)]

def Constraint.toJson (constraint : Constraint root) : Json :=
  Json.mkObj [("condition", Expr.toJson constraint.condition), ("errorMessage", Lean.toJson constraint.errorMessage),
    ("errorLocation", match constraint.errorLocation with
      | none => Json.null
      | some target => Lean.toJson (Path.toList target.path))]

namespace Runtime.JsonProtocol

def encode (refined : RefinedDataType root) (form : Form root root) (draft : DataType.denote root) : String :=
  (Json.mkObj [("version", Lean.toJson (2 : Nat)), ("schema", DataType.toJson root),
    ("constraints", Lean.toJson ((RefinedDataType.constraints refined).map Constraint.toJson)),
    ("form", Form.toJson form), ("value", valueToJson draft)]).compress

def decodeResult (refined : RefinedDataType root) (json : Json) : Except String (Option (RefinedDataType.ValidatedValue refined)) := do
  if json == Json.null then return none
  let draft ← valueFromJson root json
  match RefinedDataType.validate refined draft with
  | some value => return some value
  | none => throw ("Invalid submitted value: " ++ String.intercalate "; "
      ((RefinedDataType.errors refined draft).map (·.errorMessage)))

end Runtime.JsonProtocol

end Forms
