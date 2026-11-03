import Forms.Runtime.ExpressionProtocol.Canonical
import Forms.Runtime.ExpressionProtocol.JsonLemmas
import Std.Data.String.ToNat

namespace Forms.Runtime.ExpressionProtocol
open Lean
set_option backward.isDefEq.respectTransparency false
universe u

theorem sequenceFin_ok {n : Nat} {α : Fin n → Type}
    (values : (i : Fin n) → Except String (α i)) (result : (i : Fin n) → α i)
    (h : ∀ i, values i = .ok (result i)) : JsonProtocol.sequenceFin values = .ok result := by
  induction n with
  | zero =>
      simp only [JsonProtocol.sequenceFin, pure, Except.pure, Except.ok.injEq]
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [JsonProtocol.sequenceFin, h, bind, Except.bind]
      rw [ih _ _ (fun _ => rfl)]
      simp only [pure, Except.pure, Except.ok.injEq]
      funext i
      cases i using Fin.cases <;> rfl

private theorem transport_apply {ι : Type} {α : ι → Type} (f : (i : ι) → α i)
    {a b : ι} (h : a = b) : h ▸ f a = f b := by
  cases h
  rfl

theorem sequence_ok {ι : Type} [FinEnum ι] {α : ι → Type}
    (values : (i : ι) → Except String (α i)) (result : (i : ι) → α i)
    (h : ∀ i, values i = .ok (result i)) : JsonProtocol.sequence values = .ok result := by
  unfold JsonProtocol.sequence
  rw [sequenceFin_ok _ _ (fun i => h (FinEnum.equiv.symm i))]
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
  funext i
  exact transport_apply result (FinEnum.equiv.symm_apply_apply i)

theorem find_label (labels : Enum) (value : labels) :
    (FinEnum.toList labels).find? (fun i => labels.label i == labels.label value) = some value := by
  cases h : (FinEnum.toList labels).find? (fun i => labels.label i == labels.label value) with
  | none =>
      have := List.find?_eq_none.mp h value (FinEnum.mem_toList value)
      simp at this
  | some i =>
      have hi := List.find?_some h
      have same : i = value := labels.label_injective (by simpa using hi)
      subst i
      rfl

private theorem decode_reindex {a b : DataType} (h : a = b) (json : Json) (value : ⟦b⟧)
    (decoded : JsonProtocol.valueFromJson b json = .ok value) :
    JsonProtocol.valueFromJson a json = .ok (cast (congrArg DataType.denote h).symm value) := by
  cases h
  exact decoded

/-- Value decoding recovers the original value under the wire-type equivalence. -/
theorem value_decode
    (type : DataType) (value : ⟦type⟧) :
    JsonProtocol.valueFromJson (canonicalSchema type).dataType (JsonProtocol.valueToJson value) =
      .ok (canonicalEquiv type value) := by
  induction type with
  | text => rfl
  | boolean => cases value <;> rfl
  | natural =>
      simp [canonicalSchema, JsonProtocol.valueFromJson, JsonProtocol.valueToJson,
        Json.getStr?, toJson, Nat.toNat?_repr, bind, Except.bind, pure, Except.pure, canonicalEquiv]
  | date =>
      simp [canonicalSchema, JsonProtocol.valueFromJson, JsonProtocol.valueToJson,
        Json.getStr?, toJson, Date.ofString?_toString, bind, Except.bind, pure, Except.pure, canonicalEquiv]
  | list element ih =>
      simp only [canonicalSchema, JsonProtocol.valueFromJson, JsonProtocol.valueToJson,
        Json.getArr?, bind, Except.bind, pure, Except.pure, List.mapM_map]
      simp only [Function.comp_def, ih]
      exact List.mapM_pure (m := Except String)
  | enum labels =>
      have bound : (FinEnum.equiv value).val < labels.options.length := (enumIndex labels value).isLt
      change (if h : (FinEnum.equiv value).val < labels.options.length then
          Except.ok (⟨(FinEnum.equiv value).val, h⟩ : Fin labels.options.length)
        else Except.error "Invalid enum in interpreter result") = .ok (enumIndex labels value)
      rw [dite_eq_left bound]
      rfl
  | record labels fields ih =>
      have unique : (((FinEnum.toList labels).map
          (fun i => (labels.label i, JsonProtocol.valueToJson (value i))))).map Prod.fst |>.Nodup := by
        simpa [List.map_map, Function.comp_def, Enum.options] using labels.options_nodup
      have size := size_mkObj unique
      simp only [canonicalSchema, Schema.dataType, JsonProtocol.valueFromJson,
        JsonProtocol.valueToJson, Json.mkObj, Json.getObj?, bind, Except.bind, pure, Except.pure]
      rw [size]
      simp only [List.length_map, FinEnum.toList, List.length_map, List.length_finRange,
        domain, FinEnum.card, Enum.options, List.length_map, List.length_finRange,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      refine @sequence_ok (Fin labels.options.length) (domain labels.options labels.options_nodup).enum _ _ _ ?_
      intro j
      change ((Json.mkObj ((FinEnum.toList labels).map
        (fun i => (labels.label i, JsonProtocol.valueToJson (value i))))).getObjVal?
          (labels.options.get j)).bind
        (JsonProtocol.valueFromJson (canonicalSchema (fields ((enumIndex labels).symm j))).dataType) = _
      have label : labels.options.get j = labels.label ((enumIndex labels).symm j) := by
        simpa using enumIndex_label labels ((enumIndex labels).symm j)
      rw [label, getObjVal_mkObj unique (List.mem_map.mpr
        ⟨(enumIndex labels).symm j, FinEnum.mem_toList _, rfl⟩)]
      exact ih _ _
  | sum labels branches ih =>
      have found := find_label (domain labels.options labels.options_nodup) (enumIndex labels value.tag)
      simp only [domain, enumIndex_label] at found
      let pairs := [("tag", toJson (labels.label value.tag)),
        ("value", JsonProtocol.valueToJson (t := branches value.tag) value.payload)]
      have unique : (pairs.map Prod.fst).Nodup := by simp [pairs]
      have tag := getObjVal_mkObj unique (show ("tag", toJson (labels.label value.tag)) ∈ pairs by simp [pairs])
      have payload := getObjVal_mkObj unique (show ("value", JsonProtocol.valueToJson value.payload) ∈ pairs by simp [pairs])
      simp only [canonicalSchema, Schema.dataType, JsonProtocol.valueFromJson, JsonProtocol.valueToJson]
      rw [tag, payload]
      simp only [Json.mkObj, Json.getObj?, bind, Except.bind, pure, Except.pure]
      rw [size_mkObj unique]
      simp only [pairs, List.length_cons, List.length_nil, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, toJson, Json.getStr?, pure, Except.pure]
      rw [found]
      simp only []
      rw [decode_reindex (congrArg (fun j => (canonicalSchema (branches j)).dataType)
        ((enumIndex labels).symm_apply_apply value.tag)) _ _ (ih _ _)]
      rw [canonicalEquiv_sum]

end Forms.Runtime.ExpressionProtocol
