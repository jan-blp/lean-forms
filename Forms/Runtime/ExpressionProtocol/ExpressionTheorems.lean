module

import all Lean.Data.Json.Basic -- for JSON decoding proofs
import all Lean.Data.Json.FromToJson.Basic
import all Std.Data.TreeMap.Raw.Basic
import all Std.Data.DTreeMap.Raw.Basic
import all Std.Data.DTreeMap.Internal.Queries
import all Std.Data.DTreeMap.Internal.Operations
import all Std.Data.DTreeMap.Internal.Balancing
import all Init.Data.Ord.String
public import Forms.Runtime.ExpressionProtocol.PathTheorems
public import Forms.Runtime.ExpressionProtocol.SchemaTheorems

@[expose] public section

namespace Forms.Runtime.ExpressionProtocol
open Lean
set_option backward.isDefEq.respectTransparency false

dsimproc_decl reduceKind (expressionKind _) := okByWhnf

/-- Unfold one decoder node, rewriting its children with the hypotheses in context. -/
local macro "decode_step" : tactic =>
  `(tactic| (rw [infer.eq_def]; simp [*, reduceKind, reduceChildField, reduceChildElements,
    reduceGetObjVal, schema_decode, value_decode, path_decode, stringList_roundTrip, bool_roundTrip,
    json_toJson, Json.getObjValAs?, Json.getObjValD, Except.toOption, bind, Except.bind, Except.map,
    Except.mapError, requireType, pure, Except.pure, canonicalSchema, canonicalExpr, sequenceFin_ok]))

/-- The production decoder reconstructs every serialized expression in its wire types. -/
theorem expression_decode
    {input result : DataType} (expression : Forms.Expr input result) :
    infer (canonicalSchema input) expression.toJson = .ok ⟨canonicalSchema result, canonicalExpr expression⟩ := by
  induction expression with
  | @enumCases input result labels subject bodies hs hb =>
      have length := toList_length labels
      have row := toList_getElem labels
      decode_step
  | @cases input result labels branches subject bodies hs hb =>
      let pairs := (FinEnum.toList labels).map fun i => (labels.label i, (bodies i).toJson)
      have unique : (pairs.map Prod.fst).Nodup := by
        simpa [pairs, Function.comp_def, Enum.options] using labels.options_nodup
      have fields : checkFields (Json.mkObj pairs) labels.options = .ok () := by
        simpa [pairs, Function.comp_def, Enum.options] using checkFields_mkObj unique
      have field (i : Fin labels.options.length) :
          (Json.mkObj pairs).getObjVal? labels.options[i.val] = .ok (bodies ((enumIndex labels).symm i)).toJson :=
        getObjVal_mkObj unique <| List.mem_map.mpr ⟨(enumIndex labels).symm i, FinEnum.mem_toList _, by
          simpa using (enumIndex_label labels ((enumIndex labels).symm i)).symm⟩
      have branch := fun i => childField_ok (field i)
      simp only [pairs] at fields branch
      decode_step
  | _ => decode_step

end Forms.Runtime.ExpressionProtocol
