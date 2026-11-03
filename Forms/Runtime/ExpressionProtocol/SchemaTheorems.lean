import Forms.Runtime.ExpressionProtocol.Canonical
import Forms.Runtime.ExpressionProtocol.JsonLemmas

namespace Forms.Runtime.ExpressionProtocol
open Lean
set_option backward.isDefEq.respectTransparency false

/-- Field schemas listed in label order assemble into the canonical record or sum. -/
theorem fromFields_canonical (record : Bool) (labels : Enum) (fields : labels → DataType) :
    Schema.fromFields record ((FinEnum.toList labels).map
      (fun i => (labels.label i, canonicalSchema (fields i)))) =
      .ok (if record then canonicalSchema (.record labels fields) else canonicalSchema (.sum labels fields)) := by
  have names : ((FinEnum.toList labels).map fun i => labels.label i) = labels.options := rfl
  simp only [Schema.fromFields, List.map_map, Function.comp_def, names, labels.options_nodup, dite_true]
  cases record <;> simp [Enum.options, FinEnum.toList, enumIndex, Function.comp_def] <;>
    exact (Fin.heq_fun_iff (by simp)).2 fun _ => rfl

/-- Every serialized application type decodes to its canonical wire schema. -/
theorem schema_decode (type : DataType) :
    Schema.fromJson type.toJson = .ok (canonicalSchema type) := by
  induction type <;> rw [Schema.fromJson.eq_def] <;>
    simp [*, reduceGetObjVal, reduceCheckFields, reduceChildField, reduceChildElements,
      string_roundTrip, stringList_roundTrip, Json.getObjValAs?, Json.getObjValD, Except.toOption,
      Enum.options_nodup, List.attach_map, List.mapM_map, Function.comp_def, mapM_ok,
      fromFields_canonical, bind, Except.bind, pure, Except.pure]

end Forms.Runtime.ExpressionProtocol
