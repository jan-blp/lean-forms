import Forms.Runtime.ExpressionProtocol.Canonical
import Forms.Runtime.ExpressionProtocol.JsonLemmas

namespace Forms.Runtime.ExpressionProtocol
open Lean
set_option backward.isDefEq.respectTransparency false

theorem fromFields_record (labels : Enum) (fields : labels → DataType) :
    Schema.fromFields true ((FinEnum.toList labels).map
      (fun i => (labels.label i, canonicalSchema (fields i)))) =
      .ok (canonicalSchema (.record labels fields)) := by
  simp only [Schema.fromFields, List.map_map, Function.comp_def]
  change (if unique : labels.options.Nodup then _ else _) = _
  rw [dite_eq_left labels.options_nodup]
  simp only [↓reduceIte, canonicalSchema, Except.ok.injEq]
  congr 1
  all_goals simp [Enum.options, FinEnum.toList, enumIndex, List.get_eq_getElem, Function.comp_def]
  apply (Fin.heq_fun_iff (by simp)).2
  intro i
  rfl

theorem fromFields_sum (labels : Enum) (fields : labels → DataType) :
    Schema.fromFields false ((FinEnum.toList labels).map
      (fun i => (labels.label i, canonicalSchema (fields i)))) =
      .ok (canonicalSchema (.sum labels fields)) := by
  simp only [Schema.fromFields, List.map_map, Function.comp_def]
  change (if unique : labels.options.Nodup then _ else _) = _
  rw [dite_eq_left labels.options_nodup]
  simp only [canonicalSchema]
  all_goals simp [Enum.options, FinEnum.toList, enumIndex, List.get_eq_getElem, Function.comp_def]
  apply (Fin.heq_fun_iff (by simp)).2
  intro i
  rfl

/-- Every serialized application type decodes to its canonical wire schema. -/
theorem schema_decode (type : DataType) :
    Schema.fromJson type.toJson = .ok (canonicalSchema type) := by
  induction type with
  | text | boolean | natural | date => rw [Schema.fromJson.eq_def]; rfl
  | list element ih =>
      rw [Schema.fromJson.eq_def]
      change ((Schema.fromJson element.toJson).bind fun s => .ok (Schema.list s)) = _
      rw [ih]
      rfl
  | enum labels =>
      rw [Schema.fromJson.eq_def]
      change (do
        let names ← (fromJson? (toJson labels.options) : Except String (List String))
        if unique : names.Nodup then pure (Schema.enum names unique)
        else throw "Duplicate enum labels") = _
      rw [stringList_roundTrip]
      simp [bind, Except.bind, labels.options_nodup, pure, Except.pure, canonicalSchema]
  | record labels fields ih =>
      let entry : Json → Except String (String × Schema) := fun json => do
        checkFields json ["name", "type"]
        let name ← json.getObjValAs? String "name"
        let child ← childField json "type"
        let type ← Schema.fromJson child.val
        pure (name, type)
      have decoded (i : labels) : entry (Json.mkObj [("name", toJson (labels.label i)),
          ("type", (fields i).toJson)]) = .ok (labels.label i, canonicalSchema (fields i)) := by
        change ((Schema.fromJson (fields i).toJson).bind fun type => .ok (labels.label i, type)) = _
        rw [ih]
        rfl
      rw [Schema.fromJson.eq_def]
      change (do
        let entries ← childElements (.arr (((FinEnum.toList labels).map fun i =>
          Json.mkObj [("name", toJson (labels.label i)), ("type", (fields i).toJson)]).toArray))
        let pairs ← entries.toList.mapM (fun e => entry (Subtype.val e))
        Schema.fromFields true pairs) = _
      simp only [← bind_assoc]
      simp only [bind]
      rw [childElements_mapM (f := entry)]
      simp only [List.mapM_map, Function.comp_def]
      simp_rw [decoded]
      have hm : (FinEnum.toList labels).mapM
          (fun i => (Except.ok (labels.label i, canonicalSchema (fields i)) : Except String _)) =
          .ok ((FinEnum.toList labels).map (fun i => (labels.label i, canonicalSchema (fields i)))) :=
        List.mapM_pure (m := Except String)
      rw [hm]
      change Schema.fromFields true _ = _
      exact fromFields_record labels fields
  | sum labels fields ih =>
      let entry : Json → Except String (String × Schema) := fun json => do
        checkFields json ["name", "type"]
        let name ← json.getObjValAs? String "name"
        let child ← childField json "type"
        let type ← Schema.fromJson child.val
        pure (name, type)
      have decoded (i : labels) : entry (Json.mkObj [("name", toJson (labels.label i)),
          ("type", (fields i).toJson)]) = .ok (labels.label i, canonicalSchema (fields i)) := by
        change ((Schema.fromJson (fields i).toJson).bind fun type => .ok (labels.label i, type)) = _
        rw [ih]
        rfl
      rw [Schema.fromJson.eq_def]
      change (do
        let entries ← childElements (.arr (((FinEnum.toList labels).map fun i =>
          Json.mkObj [("name", toJson (labels.label i)), ("type", (fields i).toJson)]).toArray))
        let pairs ← entries.toList.mapM (fun e => entry (Subtype.val e))
        Schema.fromFields false pairs) = _
      simp only [← bind_assoc]
      simp only [bind]
      rw [childElements_mapM (f := entry)]
      simp only [List.mapM_map, Function.comp_def]
      simp_rw [decoded]
      have hm : (FinEnum.toList labels).mapM
          (fun i => (Except.ok (labels.label i, canonicalSchema (fields i)) : Except String _)) =
          .ok ((FinEnum.toList labels).map (fun i => (labels.label i, canonicalSchema (fields i)))) :=
        List.mapM_pure (m := Except String)
      rw [hm]
      change Schema.fromFields false _ = _
      exact fromFields_sum labels fields

end Forms.Runtime.ExpressionProtocol
