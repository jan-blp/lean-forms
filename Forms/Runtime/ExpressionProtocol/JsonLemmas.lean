import Forms.Runtime.ExpressionProtocol.Schema
import Std.Data.TreeMap.Raw.Lemmas

namespace Forms.Runtime.ExpressionProtocol
open Lean
universe u

/-- Lookup in an encoded object with distinct keys returns the encoded member. -/
theorem getObjVal_mkObj {fields : List (String × Json)}
    (unique : (fields.map Prod.fst).Nodup) {key : String} {value : Json}
    (mem : (key, value) ∈ fields) :
    (Json.mkObj fields).getObjVal? key = .ok value := by
  have distinct : fields.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    simpa [List.Nodup, List.pairwise_map] using unique
  have h := Std.TreeMap.Raw.getElem?_ofList_of_mem (cmp := compare)
    (k' := key) (by simp) distinct mem
  change (match (Std.TreeMap.Raw.ofList fields compare).get? key with
    | some v => Except.ok v | none => Except.error _) = _
  rw [show (Std.TreeMap.Raw.ofList fields compare).get? key = some value from h]

theorem size_mkObj {fields : List (String × Json)}
    (unique : (fields.map Prod.fst).Nodup) :
    (Std.TreeMap.Raw.ofList fields (cmp := compare)).size = fields.length := by
  apply Std.TreeMap.Raw.size_ofList
  simpa [List.Nodup, List.pairwise_map] using unique

private theorem forIn_ok {α β : Type} (xs : List α) (b : β)
    (f : α → β → Except String (ForInStep β))
    (h : ∀ a ∈ xs, f a b = .ok (.yield b)) : forIn xs b f = .ok b := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.forIn_cons, h a (by simp), bind, Except.bind]
      exact ih (fun a ha => h a (by simp [ha]))

theorem checkFields_mkObj {fields : List (String × Json)}
    (unique : (fields.map Prod.fst).Nodup) :
    checkFields (Json.mkObj fields) (fields.map Prod.fst) = .ok () := by
  have lookups : forIn (fields.map Prod.fst) PUnit.unit (fun name _ => do
      discard ((Json.mkObj fields).getObjVal? name)
      pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Except String PUnit) := by
    apply forIn_ok
    intro name mem
    obtain ⟨⟨key, value⟩, member, rfl⟩ := List.mem_map.mp mem
    rw [getObjVal_mkObj unique member]
    rfl
  simp only [checkFields, Json.mkObj, Json.getObj?, bind, Except.bind, pure, Except.pure] at *
  rw [lookups]
  simp [size_mkObj unique]

theorem string_roundTrip (s : String) : fromJson? (toJson s) = .ok s := rfl

theorem bool_roundTrip (b : Bool) : fromJson? (toJson b) = .ok b := by
  cases b <;> rfl

theorem json_toJson (json : Json) : toJson json = json := rfl

theorem stringList_roundTrip (xs : List String) : fromJson? (toJson xs) = .ok xs := by
  simp [fromJson?, toJson, Lean.List.fromJson?, Lean.List.toJson,
    Lean.Array.fromJson?, Lean.Array.toJson, Function.comp_def, Json.getStr?]
  rw [List.mapM_pure]
  simp [Except.map, Functor.map, pure, Except.pure]

/-- Searching by an injective key finds the element carrying that key. -/
theorem find?_key {α : Type} {xs : List α} {key : α → String} (inj : Function.Injective key)
    {x : α} (mem : x ∈ xs) : xs.find? (fun y => key y == key x) = some x := by
  cases found : xs.find? (fun y => key y == key x) with
  | none => simpa using List.find?_eq_none.mp found x mem
  | some y => simpa using inj (by simpa using List.find?_some found)

theorem mapM_ok {α β : Type} (xs : List α) (f : α → β) :
    xs.mapM (fun x => (Except.ok (f x) : Except String β)) = .ok (xs.map f) :=
  List.mapM_pure (m := Except String)

theorem sequenceFin_ok {n : Nat} {α : Fin n → Type u} (result : (i : Fin n) → α i) :
    JsonProtocol.sequenceFin (fun i => .ok (result i)) = .ok result := by
  induction n with
  | zero => simp only [JsonProtocol.sequenceFin, pure, Except.pure]; exact congrArg _ (funext (·.elim0))
  | succ n ih =>
    simp only [JsonProtocol.sequenceFin, ih, bind, Except.bind, pure, Except.pure]
    exact congrArg _ (Fin.cons_self_tail result)

open Meta Simp in
/-- Evaluate a lookup on a concrete encoded node when it succeeds definitionally. -/
def okByWhnf (e : Lean.Expr) : SimpM DStep := do
  let e' ← whnfD e
  return if e'.isAppOfArity ``Except.ok 3 then .done e' else .continue

dsimproc_decl reduceGetObjVal (Json.getObjVal? _ _) := okByWhnf
dsimproc_decl reduceCheckFields (checkFields _ _) := okByWhnf
dsimproc_decl reduceChildField (childField _ _) := okByWhnf
dsimproc_decl reduceChildElements (childElements _) := okByWhnf

end Forms.Runtime.ExpressionProtocol
