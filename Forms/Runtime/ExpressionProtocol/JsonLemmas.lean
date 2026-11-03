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

theorem stringList_roundTrip (xs : List String) : fromJson? (toJson xs) = .ok xs := by
  simp [fromJson?, toJson, Lean.List.fromJson?, Lean.List.toJson,
    Lean.Array.fromJson?, Lean.Array.toJson, Function.comp_def, Json.getStr?]
  rw [List.mapM_pure]
  simp [Except.map, Functor.map, pure, Except.pure]

theorem childElements_bind {α : Type u} (values : Array Json)
    (f : List Json → Except String α) :
    (childElements (.arr values)).bind (fun xs => f (xs.toList.map Subtype.val)) = f values.toList := by
  simp [childElements, Except.bind, List.map_map, Function.comp_def]

theorem childElements_mapM {α : Type} (values : Array Json)
    (f : Json → Except String α) :
    (childElements (.arr values)).bind (fun xs => xs.toList.mapM (fun x => f x.val)) =
      values.toList.mapM f := by
  simpa only [List.mapM_map, Function.comp_def] using childElements_bind values (fun xs => xs.mapM f)

end Forms.Runtime.ExpressionProtocol
