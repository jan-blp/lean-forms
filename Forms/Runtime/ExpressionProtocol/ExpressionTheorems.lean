import Forms.Runtime.ExpressionProtocol.PathTheorems
import Forms.Runtime.ExpressionProtocol.SchemaTheorems

namespace Forms.Runtime.ExpressionProtocol
open Lean
universe u
set_option backward.isDefEq.respectTransparency false

open Meta Simp in
/-- Evaluate a lookup on a concrete encoded node when it succeeds definitionally. -/
private def okByWhnf (e : Lean.Expr) : SimpM DStep := do
  let e' ← whnfD e
  return if e'.isAppOfArity ``Except.ok 3 then .done e' else .continue

dsimproc_decl reduceKind (expressionKind _) := okByWhnf
dsimproc_decl reduceChildField (childField _ _) := okByWhnf
dsimproc_decl reduceChildElements (childElements _) := okByWhnf
dsimproc_decl reduceGetObjVal (Json.getObjVal? _ _) := okByWhnf

private theorem bool_roundTrip (b : Bool) : fromJson? (toJson b) = .ok b := by
  cases b <;> rfl

private theorem collectFin_ok {n : Nat} {α : Fin n → Type u} (result : (i : Fin n) → α i) :
    collectFin (fun i => .ok (result i)) = .ok result := by
  induction n with
  | zero => simp only [collectFin, pure, Except.pure]; exact congrArg _ (funext (·.elim0))
  | succ n ih =>
    simp only [collectFin, ih, bind, Except.bind, pure, Except.pure]
    exact congrArg _ (Fin.cons_self_tail result)

private theorem json_toJson (json : Json) : toJson json = json := rfl

/-- Unfold one decoder node, rewriting its children with the hypotheses in context. -/
local macro "decode_step" : tactic =>
  `(tactic| (rw [infer.eq_def]; simp [*, reduceKind, reduceChildField, reduceChildElements,
    reduceGetObjVal, schema_decode, value_decode, path_decode, stringList_roundTrip, bool_roundTrip,
    json_toJson, Json.getObjValAs?, Json.getObjValD, Except.toOption, bind, Except.bind, Except.map,
    Except.mapError, requireType, pure, Except.pure, canonicalSchema, canonicalExpr, collectFin_ok]))

/-- The production decoder reconstructs every serialized expression in its wire types. -/
theorem expression_decode
    {input result : DataType} (expression : Forms.Expr input result) :
    infer (canonicalSchema input) expression.toJson = .ok ⟨canonicalSchema result, canonicalExpr expression⟩ := by
  induction expression with
  | @enumCases input result labels subject bodies hs hb =>
      have length : (FinEnum.toList labels).length = labels.options.length := by simp [Enum.options]
      have row (i : Fin labels.options.length) :
          (FinEnum.toList labels)[i.val] = (enumIndex labels).symm i := by
        simp [FinEnum.toList, enumIndex]; rfl
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
