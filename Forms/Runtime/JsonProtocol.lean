import Forms.Core.Form
import Forms.Core.RefinedDataType
import Lean.Data.Json

namespace Forms
open Lean

variable {root t target : DataType}

def DataType.toJson : DataType → Json
  | .list element => Json.mkObj [("kind", Lean.toJson "list"), ("element", element.toJson)]
  | .text => Json.mkObj [("kind", Lean.toJson "text")]
  | .boolean => Json.mkObj [("kind", Lean.toJson "boolean")]
  | .natural => Json.mkObj [("kind", Lean.toJson "natural")]
  | .choice domain => Json.mkObj [("kind", Lean.toJson "choice"), ("options", Lean.toJson domain.options)]
  | .group children => Json.mkObj [("kind", Lean.toJson "group"),
      ("children", Json.arr (Array.ofFn fun i => (children i).toJson))]

namespace Runtime.JsonProtocol

def valueToJson {t} (value : DataType.denote t) : Json :=
  match t with
  | .list element => Json.arr ((value.map (valueToJson (t := element))).toArray)
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson (toString value)
  | .choice domain => Lean.toJson (FinEnum.equiv (α := domain.type) value).val
  | .group children => Json.arr (Array.ofFn fun i => valueToJson (t := children i) (value i))

private def sequence {n : Nat} {α : Fin n → Type}
    (values : (i : Fin n) → Except String (α i)) : Except String ((i : Fin n) → α i) :=
  match n with
  | 0 => pure (fun i => Fin.elim0 i)
  | _ + 1 => do
    let head ← values 0
    let tail ← sequence (fun i => values i.succ)
    pure (Fin.cons head tail)

def valueFromJson (t : DataType) (json : Json) : Except String (DataType.denote t) :=
  match t with
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
  | .choice domain => do
    let index ← json.getNat?
    if h : index < FinEnum.card domain.type then return FinEnum.equiv.symm ⟨index, h⟩
    else throw "Invalid choice in interpreter result"
  | @DataType.group n children => do
    let items ← json.getArr?
    if h : items.size = n then
      sequence (fun i => valueFromJson (children i) (items[i.val]'(by omega)))
    else throw "Wrong number of group values in interpreter result"

end Runtime.JsonProtocol

def Path.toList {root target} : Path root target → List Nat
  | .here => []
  | .child index rest => index.val :: Path.toList rest

def Expr.toJson {root t} : Expr root t → Json
  | .value v => Json.mkObj [("kind", Lean.toJson "value"), ("type", DataType.toJson t), ("value", Runtime.JsonProtocol.valueToJson v)]
  | .project p => Json.mkObj [("kind", Lean.toJson "project"), ("path", Lean.toJson (Path.toList p))]
  | .all items predicate => Json.mkObj [("kind", Lean.toJson "all"),
      ("items", items.toJson), ("predicate", predicate.toJson)]
  | .and l r => binary "and" (Expr.toJson l) (Expr.toJson r)
  | .natLe l r => binary "natLe" (Expr.toJson l) (Expr.toJson r)
where
  binary (kind : String) (left right : Json) : Json :=
    Json.mkObj [("kind", Lean.toJson kind), ("left", left), ("right", right)]

def Widget.name : Widget t → String
  | .textInput => "textInput"
  | .checkbox => "checkbox"
  | .naturalInput => "naturalInput"
  | .select => "select"

def Form.toJson {root t} : Form root t → Json
  | .list label item defaultItem => Json.mkObj [("kind", Lean.toJson "list"),
      ("label", Lean.toJson label), ("item", item.toJson),
      ("defaultItem", Runtime.JsonProtocol.valueToJson defaultItem)]
  | .field label widget => Json.mkObj [("kind", Lean.toJson "field"), ("label", Lean.toJson label),
      ("widget", Lean.toJson (Widget.name widget))]
  | .group label children => Json.mkObj [("kind", Lean.toJson "group"), ("label", Lean.toJson label),
      ("children", Json.arr (Array.ofFn fun i => (children i).toJson))]
  | .visibleWhen condition body => Json.mkObj [("kind", Lean.toJson "visibleWhen"),
      ("condition", Expr.toJson condition), ("body", Form.toJson body)]

def Constraint.toJson (constraint : Constraint root) : Json :=
  Json.mkObj [("condition", Expr.toJson constraint.condition), ("errorMessage", Lean.toJson constraint.errorMessage),
    ("errorLocation", match constraint.errorLocation with
      | none => Json.null
      | some target => Lean.toJson (Path.toList target.path))]

namespace Runtime.JsonProtocol

def encode (refined : RefinedDataType root) (form : Form root root) (draft : DataType.denote root) : String :=
  (Json.mkObj [("version", Lean.toJson (2 : Nat)), ("schema", DataType.toJson root),
    ("constraints", Lean.toJson (refined.constraints.map Constraint.toJson)),
    ("form", Form.toJson form), ("value", valueToJson draft)]).compress

def decodeResult (refined : RefinedDataType root) (json : Json) : Except String (Option refined.denote) := do
  if json == Json.null then return none
  let draft ← valueFromJson root json
  match refined.validate draft with
  | some value => return some value
  | none => throw ("Invalid submitted value: " ++ String.intercalate "; "
      ((refined.errors draft).map (·.errorMessage)))

end Runtime.JsonProtocol

end Forms
