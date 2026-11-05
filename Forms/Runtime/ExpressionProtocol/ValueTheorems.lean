module

import all Lean.Data.Json.Basic -- for JSON decoding proofs
import all Lean.Data.Json.FromToJson.Basic
import all Std.Data.TreeMap.Raw.Basic
import all Std.Data.DTreeMap.Raw.Basic
import all Std.Data.DTreeMap.Internal.Queries
import all Std.Data.DTreeMap.Internal.Operations
import all Std.Data.DTreeMap.Internal.Balancing
import all Init.Data.Ord.String
public import Forms.Runtime.ExpressionProtocol.Canonical
public import Forms.Runtime.ExpressionProtocol.JsonLemmas
public import Std.Data.String.ToNat
public import Forms.Core.Date.Theorems

@[expose] public section

namespace Forms.Runtime.ExpressionProtocol
open Lean
set_option backward.isDefEq.respectTransparency false

theorem transport_apply {ι : Type} {α : ι → Type} (f : (i : ι) → α i)
    {a b : ι} (h : a = b) : h ▸ f a = f b := by
  cases h
  rfl

theorem sequence_ok {ι : Type} [FinEnum ι] {α : ι → Type} (result : (i : ι) → α i) :
    JsonProtocol.sequence (fun i => .ok (result i)) = .ok result := by
  simp only [JsonProtocol.sequence, sequenceFin_ok, bind, Except.bind, pure, Except.pure]
  exact congrArg _ (funext fun i => transport_apply result (FinEnum.equiv.symm_apply_apply i))

theorem decode_reindex {a b : DataType} (h : a = b) (json : Json) (value : ⟦b⟧)
    (decoded : JsonProtocol.valueFromJson b json = .ok value) :
    JsonProtocol.valueFromJson a json = .ok (cast (congrArg DataType.denote h).symm value) := by
  cases h
  exact decoded

theorem getObj_mkObj (fields : List (String × Json)) :
    (Json.mkObj fields).getObj? = .ok (Std.TreeMap.Raw.ofList fields compare) := by rfl

theorem getNat_fromNat (n : Nat) : (Json.num (JsonNumber.fromNat n)).getNat? = .ok n := by rfl

/-- Value decoding recovers the original value under the wire-type equivalence. -/
theorem value_decode
    (type : DataType) (value : ⟦type⟧) :
    JsonProtocol.valueFromJson (canonicalSchema type).dataType (JsonProtocol.valueToJson value) =
      .ok (canonicalEquiv type value) := by
  induction type with
  | enum labels =>
      have bound : (FinEnum.equiv value).val < labels.options.length := (enumIndex labels value).isLt
      simp [JsonProtocol.valueFromJson, JsonProtocol.valueToJson, toJson, getNat_fromNat, bound,
        bind, Except.bind, pure, Except.pure]
      rfl
  | record labels fields ih =>
      let pairs := (FinEnum.toList labels).map fun i => (labels.label i, JsonProtocol.valueToJson (value i))
      have unique : (pairs.map Prod.fst).Nodup := by
        simpa [pairs, Function.comp_def, Enum.options] using labels.options_nodup
      have size := size_mkObj unique
      have field (i : labels) : (Json.mkObj pairs).getObjVal? (labels.label i) =
          .ok (JsonProtocol.valueToJson (value i)) :=
        getObjVal_mkObj unique (List.mem_map.mpr ⟨i, FinEnum.mem_toList i, rfl⟩)
      simp only [pairs] at size field
      simp [JsonProtocol.valueFromJson, JsonProtocol.valueToJson, getObj_mkObj, size, field, ih,
        toList_getElem, sequence_ok, Enum.options, bind, Except.bind]
      rfl
  | sum labels branches ih =>
      have found := find?_key (domain labels.options labels.options_nodup).label_injective
        (@FinEnum.mem_toList _ (domain labels.options labels.options_nodup).enum (enumIndex labels value.tag))
      simp only [domain, enumIndex_label] at found
      have size := size_mkObj (fields := [("tag", toJson (labels.label value.tag)),
        ("value", JsonProtocol.valueToJson value.payload)]) (by simp)
      simp [JsonProtocol.valueFromJson, JsonProtocol.valueToJson, getObj_mkObj, reduceGetObjVal,
        Json.getStr?, toJson, bind, Except.bind, pure, Except.pure] at size found ⊢
      simp only [size, found, ↓reduceIte]
      rw [decode_reindex (congrArg (fun j => (canonicalSchema (branches j)).dataType)
        ((enumIndex labels).symm_apply_apply value.tag)) _ _ (ih _ _), canonicalEquiv_sum]
  | _ =>
      simp_all [JsonProtocol.valueFromJson, JsonProtocol.valueToJson, Json.getStr?, Json.getBool?,
        Json.getArr?, toJson, Nat.toNat?_repr, Date.ofString?_toString, List.mapM_map, Function.comp_def,
        mapM_ok, canonicalEquiv, Equiv.listEquivOfEquiv, bind, Except.bind, pure, Except.pure]

end Forms.Runtime.ExpressionProtocol
