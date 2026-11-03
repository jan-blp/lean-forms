import Forms.Runtime.ExpressionProtocol.JsonChildren

namespace Forms.Runtime.ExpressionProtocol
open Lean
universe u

/-- A wire schema has canonical finite indices, unlike application-defined enums. -/
inductive Schema where
  | text | boolean | natural | date
  | enum (names : List String) (unique : names.Nodup)
  | list (element : Schema)
  | record (names : List String) (unique : names.Nodup) (fields : Fin names.length → Schema)
  | sum (names : List String) (unique : names.Nodup) (branches : Fin names.length → Schema)

def Schema.decEq (a b : Schema) : Decidable (a = b) :=
  match a, b with
  | .text, .text | .boolean, .boolean | .natural, .natural | .date, .date => isTrue rfl
  | .enum names unique, .enum other otherUnique =>
      decidable_of_iff (names = other) (by simp)
  | .list element, .list other =>
      letI := Schema.decEq element other
      decidable_of_iff (element = other) (by simp)
  | .record names unique fields, .record other otherUnique otherFields =>
      if h : names = other then by
        subst other
        letI := fun i => Schema.decEq (fields i) (otherFields i)
        exact decidable_of_iff (∀ i, fields i = otherFields i) (by simp [funext_iff])
      else isFalse (by intro same; cases same; exact h rfl)
  | .sum names unique branches, .sum other otherUnique otherBranches =>
      if h : names = other then by
        subst other
        letI := fun i => Schema.decEq (branches i) (otherBranches i)
        exact decidable_of_iff (∀ i, branches i = otherBranches i) (by simp [funext_iff])
      else isFalse (by intro same; cases same; exact h rfl)
  | .text, .boolean | .text, .natural | .text, .date | .text, .enum .. | .text, .list .. | .text, .record .. | .text, .sum ..
  | .boolean, .text | .boolean, .natural | .boolean, .date | .boolean, .enum .. | .boolean, .list .. | .boolean, .record .. | .boolean, .sum ..
  | .natural, .text | .natural, .boolean | .natural, .date | .natural, .enum .. | .natural, .list .. | .natural, .record .. | .natural, .sum ..
  | .date, .text | .date, .boolean | .date, .natural | .date, .enum .. | .date, .list .. | .date, .record .. | .date, .sum ..
  | .enum .., .text | .enum .., .boolean | .enum .., .natural | .enum .., .date | .enum .., .list .. | .enum .., .record .. | .enum .., .sum ..
  | .list .., .text | .list .., .boolean | .list .., .natural | .list .., .date | .list .., .enum .. | .list .., .record .. | .list .., .sum ..
  | .record .., .text | .record .., .boolean | .record .., .natural | .record .., .date | .record .., .enum .. | .record .., .list .. | .record .., .sum ..
  | .sum .., .text | .sum .., .boolean | .sum .., .natural | .sum .., .date | .sum .., .enum .. | .sum .., .list .. | .sum .., .record .. => isFalse (by intro h; cases h)
termination_by structural a

instance : DecidableEq Schema := Schema.decEq

abbrev domain (names : List String) (unique : names.Nodup) : Enum where
  type := Fin names.length
  enum := { card := names.length, equiv := Equiv.refl _ }
  label := names.get
  label_injective := fun _ _ h => unique.get_inj_iff.mp h

abbrev Schema.dataType : Schema → DataType
  | .text => .text
  | .boolean => .boolean
  | .natural => .natural
  | .date => .date
  | .enum names unique => .enum (domain names unique)
  | .list element => .list element.dataType
  | .record names unique fields => .record (domain names unique) (fun i => (fields i).dataType)
  | .sum names unique branches => .sum (domain names unique) (fun i => (branches i).dataType)

/-- Require exactly the protocol fields, including for objects built without parsing text. -/
def checkFields (json : Json) (names : List String) : Except String Unit := do
  let object ← json.getObj?
  for name in names do discard <| json.getObjVal? name
  if object.size != names.length then throw "Unexpected object fields"

/-- Sequence a finite family without dropping its dependent index. -/
def collectFin {n : Nat} {α : Fin n → Type u}
    (values : (i : Fin n) → Except String (α i)) : Except String ((i : Fin n) → α i) :=
  match n with
  | 0 => pure (fun i => Fin.elim0 i)
  | _ + 1 => do
    let head ← values 0
    let tail ← collectFin (fun i => values i.succ)
    pure (Fin.cons head tail)

/-- Assemble a record or sum after decoding its named fields. -/
def Schema.fromFields (record : Bool) (pairs : List (String × Schema)) : Except String Schema :=
  let names := pairs.map Prod.fst
  if unique : names.Nodup then
    let fields := fun (i : Fin names.length) =>
      (pairs.get ⟨i.val, by simpa [names] using i.isLt⟩).2
    if record then .ok (.record names unique fields)
    else .ok (.sum names unique fields)
  else .error "Duplicate field or constructor names"

def Schema.fromJson (json : Json) : Except String Schema := do
  let kind ← json.getObjValAs? String "kind"
  match kind with
  | "text" => checkFields json ["kind"]; return .text
  | "boolean" => checkFields json ["kind"]; return .boolean
  | "natural" => checkFields json ["kind"]; return .natural
  | "date" => checkFields json ["kind"]; return .date
  | "list" =>
      checkFields json ["kind", "element"]
      return .list (← fromJson (← childField json "element").val)
  | "enum" =>
      checkFields json ["kind", "options"]
      let names ← json.getObjValAs? (List String) "options"
      if unique : names.Nodup then return .enum names unique
      else throw "Duplicate enum labels"
  | "record" | "sum" =>
      let key := if kind == "record" then "fields" else "constructors"
      checkFields json ["kind", key]
      let container ← childField json key
      let entries ← childElements container.val
      let pairs ← entries.toList.mapM fun entry => do
        checkFields entry.val ["name", "type"]
        return (← entry.val.getObjValAs? String "name", ← fromJson (← childField entry.val "type").val)
      Schema.fromFields (kind == "record") pairs
  | _ => throw s!"Unknown schema kind: {kind}"

termination_by sizeOf json
decreasing_by all_goals decreasing_tactic

end Forms.Runtime.ExpressionProtocol
