module

public import Forms.Core.Widget
public import Forms.Core.RefinedDataType
public import Lean.Data.Json
import all Lean.Data.Json.Basic -- for the date decoder's round-trip proof

@[expose] public section

namespace Forms
universe u

open Lean

variable {root input context t : DataType}

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

/-- Sequence a finite family without dropping its dependent index. -/
def sequenceFin {n : Nat} {α : Fin n → Type u}
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
      | throw "Invalid sum tag in value"
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
    -- `String.toNat?` also accepts `_` separators.
    match if text.all Char.isDigit then text.toNat? else none with
    | some n => pure n
    | none => throw "Invalid natural in value"
  | .enum domain => do
    let index ← json.getNat?
    if h : index < FinEnum.card domain then return FinEnum.equiv.symm ⟨index, h⟩
    else throw "Invalid enum in value"
  | .record fieldNames fieldTypes => do
    let object ← json.getObj?
    if object.size != FinEnum.card fieldNames then
      throw "Wrong number of record fields in value"
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
  | .locations locs _ => Json.mkObj [
      ("kind", Lean.toJson "locations"), ("locations", Lean.toJson (locs.map Location.toJson))]

def ResolvedError.toJson {root : DataType} (error : ResolvedError root) : Json :=
  Json.mkObj [("message", Lean.toJson error.message), ("targets", error.targets.toJson)]

end Forms.Validation
