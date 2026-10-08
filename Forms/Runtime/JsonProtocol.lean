import Forms.Core.Form
import Lean.Data.Json

namespace Forms
open Lean

def DataType.toJson : DataType → Json
  | .text => Json.mkObj [("kind", Lean.toJson "text")]
  | .boolean => Json.mkObj [("kind", Lean.toJson "boolean")]
  | .natural => Json.mkObj [("kind", Lean.toJson "natural")]
  | .group children => Json.mkObj [("kind", Lean.toJson "group"),
      ("children", Json.arr (Array.ofFn fun i => (children i).toJson))]

namespace Runtime.JsonProtocol

def valueToJson {type : DataType} (value : DataType.denote type) : Json :=
  match type with
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson (toString value)
  | .group children => Json.arr (Array.ofFn fun i => valueToJson (type := children i) (value i))

private def sequence {n : Nat} {α : Fin n → Type}
    (values : (i : Fin n) → Except String (α i)) : Except String ((i : Fin n) → α i) :=
  match n with
  | 0 => pure (fun i => Fin.elim0 i)
  | _ + 1 => do
    let head ← values 0
    let tail ← sequence (fun i => values i.succ)
    pure (Fin.cons head tail)

def valueFromJson (type : DataType) (json : Json) : Except String (DataType.denote type) :=
  match type with
  | .text => json.getStr?
  | .boolean => json.getBool?
  | .natural => do
    let text ← json.getStr?
    match text.toNat? with
    | some n => pure n
    | none => throw "Invalid natural in interpreter result"
  | @DataType.group n children => do
    let items ← json.getArr?
    if h : items.size = n then
      sequence (fun i => valueFromJson (children i) (items[i.val]'(by omega)))
    else throw "Wrong number of group values in interpreter result"

end Runtime.JsonProtocol

def Path.toList {root target : DataType} : Path root target → List Nat
  | .here => []
  | .child index rest => index.val :: Path.toList rest

def Expr.toJson {root type : DataType} : Expr root type → Json
  | .value v => Json.mkObj [("kind", Lean.toJson "value"), ("type", DataType.toJson type), ("value", Runtime.JsonProtocol.valueToJson v)]
  | .project p => Json.mkObj [("kind", Lean.toJson "project"), ("path", Lean.toJson (Path.toList p))]
  | .and l r => binary "and" (Expr.toJson l) (Expr.toJson r)
  | .natLe l r => binary "natLe" (Expr.toJson l) (Expr.toJson r)
where
  binary (kind : String) (left right : Json) : Json :=
    Json.mkObj [("kind", Lean.toJson kind), ("left", left), ("right", right)]

def Widget.name {type : DataType} : Widget type → String
  | .textInput => "textInput"
  | .checkbox => "checkbox"
  | .naturalInput => "naturalInput"

def Form.toJson {root type : DataType} : Form root type → Json
  | .field label widget => Json.mkObj [("kind", Lean.toJson "field"), ("label", Lean.toJson label),
      ("widget", Lean.toJson (Widget.name widget))]
  | .group label children => Json.mkObj [("kind", Lean.toJson "group"), ("label", Lean.toJson label),
      ("children", Json.arr (Array.ofFn fun i => (children i).toJson))]
  | .visibleWhen condition body => Json.mkObj [("kind", Lean.toJson "visibleWhen"),
      ("condition", Expr.toJson condition), ("body", Form.toJson body)]

namespace Runtime.JsonProtocol

def encode {root : DataType} (form : Form root root) (value : DataType.denote root) : String :=
  (Json.mkObj [("version", Lean.toJson (1 : Nat)), ("schema", DataType.toJson root),
    ("form", Form.toJson form), ("value", valueToJson value)]).compress

end Runtime.JsonProtocol

end Forms
