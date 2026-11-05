module

public import Forms.Core.Widget
public import Forms.Core.RefinedDataType
public import Lean.Data.Json
import all Lean.Data.Json.Basic -- for the date decoder's round-trip proof

@[expose] public section

namespace Forms

open Lean

variable {root input context t : DataType}

def DataType.toJson (t : DataType) : Json :=
  match t with
  | .sum tags constructors => Json.mkObj [("kind", Lean.toJson "sum"),
      ("constructors", Json.arr ((FinEnum.toList tags).map fun i =>
        Json.mkObj [("name", Lean.toJson (tags.label i)), ("type", DataType.toJson (constructors i))]).toArray)]
  | .list element => Json.mkObj [("kind", Lean.toJson "list"), ("element", DataType.toJson element)]
  | .text => Json.mkObj [("kind", Lean.toJson "text")]
  | .boolean => Json.mkObj [("kind", Lean.toJson "boolean")]
  | .date => Json.mkObj [("kind", Lean.toJson "date")]
  | .natural => Json.mkObj [("kind", Lean.toJson "natural")]
  | .enum domain => Json.mkObj [("kind", Lean.toJson "enum"), ("options", Lean.toJson (Enum.options domain))]
  | .record fieldNames fieldTypes => Json.mkObj [("kind", Lean.toJson "record"),
      ("fields", Json.arr ((FinEnum.toList fieldNames).map fun i =>
        Json.mkObj [("name", Lean.toJson (fieldNames.label i)), ("type", DataType.toJson (fieldTypes i))]).toArray)]

namespace Runtime.JsonProtocol

def valueToJson {t} (value : ⟦t⟧) : Json :=
  match t with
  | .sum tags constructors => Json.mkObj [("tag", Lean.toJson (tags.label value.tag)),
      ("value", valueToJson (t := constructors value.tag) value.payload)]
  | .list element => Json.arr ((value.map (valueToJson (t := element))).toArray)
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .date => Lean.toJson (Date.toString value)
  | .natural => Lean.toJson (toString value)
  | .enum domain => Lean.toJson (FinEnum.equiv (α := domain) value).val
  | .record fieldNames fieldTypes => Json.mkObj ((FinEnum.toList fieldNames).map fun i =>
      (fieldNames.label i, valueToJson (t := fieldTypes i) (value i)))

def sequenceFin {n : Nat} {α : Fin n → Type}
  (values : (i : Fin n) → Except String (α i))
  : Except String ((i : Fin n) → α i) :=
  match n with
  | 0 => pure (fun i => Fin.elim0 i)
  | _ + 1 => do
    let head ← values 0
    let tail ← sequenceFin (fun i => values i.succ)
    pure (Fin.cons head tail)

def sequence {ι : Type}
  [FinEnum ι]
  {α : ι → Type}
  (values : (i : ι) → Except String (α i))
  : Except String ((i : ι) → α i) := do
  let result ← sequenceFin (fun i => values (FinEnum.equiv.symm i))
  pure fun i => (FinEnum.equiv.symm_apply_apply i) ▸ result (FinEnum.equiv i)

def valueFromJson (t : DataType) (json : Json) : Except String ⟦t⟧ :=
  match t with
  | .sum tags constructors => do
    let fields ← json.getObj?
    if fields.size != 2 then throw "Expected only tag and value in sum"
    let name ← (← json.getObjVal? "tag").getStr?
    let some tag := (FinEnum.toList tags).find? (fun i => tags.label i == name)
      | throw "Invalid sum tag in interpreter result"
    let payload ← valueFromJson (constructors tag) (← json.getObjVal? "value")
    return ⟨tag, payload⟩
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
  (h : valueFromJson .date json = .ok date)
  : valueToJson (t := .date) date = json := by
  cases json <;>
    simp_all [valueFromJson, Json.getStr?, bind, Except.bind, pure, Except.pure,
      valueToJson, toJson]
  split at h <;> simp_all
  grind [Date.ofString?_sound]

end Runtime.JsonProtocol

def Path.toList {source target : DataType}
  (path : Path source target)
  : List String :=
  match path with
  | .self => []
  | .field (fieldNames := fieldNames) fieldName rest => fieldNames.label fieldName :: Path.toList rest

def Expr.toJson {input t} (expression : Expr input t) : Json :=
  match expression with
  | .value v => Json.mkObj [("kind", Lean.toJson "value"), ("type", DataType.toJson t), ("value", Runtime.JsonProtocol.valueToJson v)]
  | .project p => Json.mkObj [("kind", Lean.toJson "project"), ("path", Lean.toJson (Path.toList p))]
  | .all items predicate => Json.mkObj [("kind", Lean.toJson "all"),
      ("items", Expr.toJson items), ("predicate", Expr.toJson predicate)]
  | .cases (tags := tags) subject branches => Json.mkObj [("kind", Lean.toJson "cases"),
      ("type", DataType.toJson t), ("subject", Expr.toJson subject),
      ("branches", Json.mkObj ((FinEnum.toList tags).map fun i => (tags.label i, Expr.toJson (branches i))))]
  | .sum items expression => Json.mkObj [("kind", Lean.toJson "sum"),
      ("items", Expr.toJson items), ("expression", Expr.toJson expression)]
  | .filter items predicate => Json.mkObj [("kind", Lean.toJson "filter"),
      ("items", Expr.toJson items), ("predicate", Expr.toJson predicate)]
  | .sortBy items key descending => Json.mkObj [("kind", Lean.toJson "sortBy"),
      ("items", Expr.toJson items), ("key", Expr.toJson key), ("descending", Lean.toJson descending)]
  | .search items key query => Json.mkObj [("kind", Lean.toJson "search"),
      ("items", Expr.toJson items), ("key", Expr.toJson key), ("query", Expr.toJson query)]
  | .sortNatBy items key descending => Json.mkObj [("kind", Lean.toJson "sortNatBy"),
      ("items", Expr.toJson items), ("key", Expr.toJson key), ("descending", Lean.toJson descending)]
  | .snoc items expression => Json.mkObj [("kind", Lean.toJson "snoc"),
      ("items", Expr.toJson items), ("value", Expr.toJson expression)]
  | .length items => Json.mkObj [("kind", Lean.toJson "length"), ("items", Expr.toJson items)]
  | .enumCases (domain := domain) subject branches => Json.mkObj [("kind", Lean.toJson "enumCases"),
      ("type", DataType.toJson t), ("subject", Expr.toJson subject),
      ("branches", Lean.toJson ((FinEnum.toList domain).map fun choice => Expr.toJson (branches choice)))]
  | .enumEq left right => binary "enumEq" (Expr.toJson left) (Expr.toJson right)
  | .enumLabel (domain := domain) subject => Json.mkObj [("kind", Lean.toJson "enumLabel"),
      ("options", Lean.toJson (Enum.options domain)), ("subject", Expr.toJson subject)]
  | .ifThenElse condition whenTrue whenFalse => Json.mkObj [("kind", Lean.toJson "ifThenElse"),
      ("condition", Expr.toJson condition), ("whenTrue", Expr.toJson whenTrue), ("whenFalse", Expr.toJson whenFalse)]
  | .natToText operand => Json.mkObj [("kind", Lean.toJson "natToText"), ("operand", Expr.toJson operand)]
  | .textEq left right => binary "textEq" (Expr.toJson left) (Expr.toJson right)
  | .textAppend left right => binary "textAppend" (Expr.toJson left) (Expr.toJson right)
  | .natAdd l r => binary "natAdd" (Expr.toJson l) (Expr.toJson r)
  | .natSub l r => binary "natSub" (Expr.toJson l) (Expr.toJson r)
  | .natMul l r => binary "natMul" (Expr.toJson l) (Expr.toJson r)
  | .not operand => Json.mkObj [("kind", Lean.toJson "not"), ("operand", Expr.toJson operand)]
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

end Forms

namespace Forms.Validation

open Lean

def Location.toList {root : DataType} : Location root → List Json
  | .self => []
  | .field (fieldNames := names) name rest =>
      Json.mkObj [("kind", Lean.toJson "field"), ("name", Lean.toJson (names.label name))] :: rest.toList
  | .item index rest =>
      Json.mkObj [("kind", Lean.toJson "item"), ("index", Lean.toJson (toString index))] :: rest.toList
  | .constructor (tags := tags) tag rest =>
      Json.mkObj [("kind", Lean.toJson "constructor"), ("tag", Lean.toJson (tags.label tag))] :: rest.toList

def Location.toJson {root : DataType} (location : Location root) : Json :=
  Lean.toJson location.toList

def TargetResolution.toJson {root : DataType} : TargetResolution root → Json
  | .global => Json.mkObj [("kind", Lean.toJson "global")]
  | .fields locations _ => Json.mkObj [
      ("kind", Lean.toJson "fields"), ("locations", Lean.toJson (locations.map Location.toJson))]
  | .invalidTarget location => Json.mkObj [
      ("kind", Lean.toJson "invalidTarget"), ("location", Location.toJson location)]

def ResolvedError.toJson {root : DataType} (error : ResolvedError root) : Json :=
  Json.mkObj [("message", Lean.toJson error.message), ("targets", error.targets.toJson)]

def LocationExpr.toJson {input target : DataType} : LocationExpr input target → List Json
  | .self => []
  | .field (fieldNames := names) name rest =>
      Json.mkObj [("kind", Lean.toJson "field"), ("name", Lean.toJson (names.label name))] :: rest.toJson
  | .item index rest => Json.mkObj [("kind", Lean.toJson "item"), ("index", index.toJson)] :: rest.toJson
  | .constructor (tags := tags) tag rest =>
      Json.mkObj [("kind", Lean.toJson "constructor"), ("tag", Lean.toJson (tags.label tag))] :: rest.toJson

def TargetsExpr.toJson {root input : DataType} : TargetsExpr root input → Json
  | .global => Json.mkObj [("kind", Lean.toJson "global")]
  | .fields locations _ => Json.mkObj [
      ("kind", Lean.toJson "fields"),
      ("locations", Lean.toJson (locations.map LocationExpr.toJson))]

def ScopedChecker.toJson {root input : DataType} : ScopedChecker root input → Json
  | .pass => Json.mkObj [("kind", Lean.toJson "pass")]
  | .report message targets => Json.mkObj [
      ("kind", Lean.toJson "report"), ("message", message.toJson), ("targets", targets.toJson)]
  | .when condition body => Json.mkObj [
      ("kind", Lean.toJson "when"), ("condition", condition.toJson), ("body", body.toJson)]
  | .seq left right => Json.mkObj [
      ("kind", Lean.toJson "seq"), ("left", left.toJson), ("right", right.toJson)]
  | .each items body => Json.mkObj [
      ("kind", Lean.toJson "each"), ("items", items.toJson), ("body", body.toJson)]

end Forms.Validation

namespace Forms

def RefinedDataType.toJson {ty : DataType}
  (refined : RefinedDataType ty)
  : Lean.Json :=
  match refined with
  | .base _ => Lean.Json.mkObj [("kind", Lean.toJson "base")]
  | .serverRefine inner _ => inner.toJson
  | .refine inner checked => Lean.Json.mkObj [
      ("kind", Lean.toJson "refine"), ("inner", inner.toJson), ("checker", checked.checker.toJson)]
  | .list item => Lean.Json.mkObj [("kind", Lean.toJson "list"), ("item", item.toJson)]
  | .record (fieldNames := names) fields => Lean.Json.mkObj [
      ("kind", Lean.toJson "record"),
      ("fields", Lean.Json.mkObj ((FinEnum.toList names).map fun name => (names.label name, (fields name).toJson)))]
  | .sum (tags := tags) branches => Lean.Json.mkObj [
      ("kind", Lean.toJson "sum"),
      ("branches", Lean.Json.mkObj ((FinEnum.toList tags).map fun tag => (tags.label tag, (branches tag).toJson)))]

end Forms
