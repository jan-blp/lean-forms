import Forms.Runtime.ExpressionProtocol.PathTheorems
import Forms.Runtime.ExpressionProtocol.SchemaTheorems

namespace Forms.Runtime.ExpressionProtocol
open Lean
universe u
set_option backward.isDefEq.respectTransparency false

private def readJson (input : Schema) (kind key : String) (json : Json) :=
  (infer input json).mapError (fun error => s!"{kind}.{key}: {error}")

private def checkJson (input expected : Schema) (kind key : String) (json : Json) :
    Except String (Forms.Expr input.dataType expected.dataType) := do
  requireType expected (← readJson input kind key json)

private theorem readJson_ok {input result : DataType} {expression : Forms.Expr input result}
    (kind key : String)
    (h : infer (canonicalSchema input) expression.toJson = .ok ⟨canonicalSchema result, canonicalExpr expression⟩) :
    readJson (canonicalSchema input) kind key expression.toJson =
      .ok ⟨canonicalSchema result, canonicalExpr expression⟩ := by
  simp [readJson, h, Except.mapError]

private theorem checkJson_ok {input result : DataType} {expression : Forms.Expr input result}
    (kind key : String)
    (h : infer (canonicalSchema input) expression.toJson = .ok ⟨canonicalSchema result, canonicalExpr expression⟩) :
    checkJson (canonicalSchema input) (canonicalSchema result) kind key expression.toJson =
      .ok (canonicalExpr expression) := by
  simp [checkJson, readJson, h, Except.mapError, requireType, bind, Except.bind]

private theorem collectFin_ok {n : Nat} {α : Fin n → Type u}
    (values : (i : Fin n) → Except String (α i)) (result : (i : Fin n) → α i)
    (h : ∀ i, values i = .ok (result i)) : collectFin values = .ok result := by
  induction n with
  | zero =>
      simp only [collectFin, pure, Except.pure, Except.ok.injEq]
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [collectFin, h, bind, Except.bind]
      rw [ih _ _ (fun _ => rfl)]
      simp only [pure, Except.pure, Except.ok.injEq]
      funext i
      cases i using Fin.cases <;> rfl

/-- The production decoder reconstructs every serialized expression in its wire types. -/
theorem expression_decode
    {input result : DataType} (expression : Forms.Expr input result) :
    infer (canonicalSchema input) expression.toJson = .ok ⟨canonicalSchema result, canonicalExpr expression⟩ := by
  induction expression with
  | @value input result value =>
      rw [infer.eq_def]
      change ((Schema.fromJson result.toJson).bind fun schema =>
        (JsonProtocol.valueFromJson schema.dataType (JsonProtocol.valueToJson value)).map
          fun v => (⟨schema, .value v⟩ : Decoded (canonicalSchema input))) = _
      rw [schema_decode]
      simp only [Except.bind, value_decode, Except.map, canonicalExpr]
  | @project input result path =>
      have parsed : (Forms.Expr.project path).toJson.getObjValAs? (List String) "path" = .ok path.toList := by
        change fromJson? (toJson path.toList) = _
        exact stringList_roundTrip _
      rw [infer.eq_def]
      change ((Forms.Expr.project path).toJson.getObjValAs? (List String) "path").bind
        (fun labels => (pathFromLabels (canonicalSchema input) labels).map
          (fun ⟨schema, p⟩ => (⟨schema, .project p⟩ : Decoded (canonicalSchema input)))) = _
      rw [parsed]
      simp only [Except.bind, path_decode, Except.map, canonicalExpr]
  | @natAdd input left right hl hr =>
      rw [infer.eq_def]
      change (do
        let l ← checkJson (canonicalSchema input) .natural "natAdd" "left" left.toJson
        let r ← checkJson (canonicalSchema input) .natural "natAdd" "right" right.toJson
        pure (⟨.natural, .natAdd l r⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ hl]
      simp only [bind, Except.bind]
      rw [checkJson_ok _ _ hr]
      rfl
  | @natSub input left right hl hr =>
      rw [infer.eq_def]
      change (do
        let l ← checkJson (canonicalSchema input) .natural "natSub" "left" left.toJson
        let r ← checkJson (canonicalSchema input) .natural "natSub" "right" right.toJson
        pure (⟨.natural, .natSub l r⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ hl]
      simp only [bind, Except.bind]
      rw [checkJson_ok _ _ hr]
      rfl
  | @natMul input left right hl hr =>
      rw [infer.eq_def]
      change (do
        let l ← checkJson (canonicalSchema input) .natural "natMul" "left" left.toJson
        let r ← checkJson (canonicalSchema input) .natural "natMul" "right" right.toJson
        pure (⟨.natural, .natMul l r⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ hl]
      simp only [bind, Except.bind]
      rw [checkJson_ok _ _ hr]
      rfl
  | @natLe input left right hl hr =>
      rw [infer.eq_def]
      change (do
        let l ← checkJson (canonicalSchema input) .natural "natLe" "left" left.toJson
        let r ← checkJson (canonicalSchema input) .natural "natLe" "right" right.toJson
        pure (⟨.boolean, .natLe l r⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ hl]
      simp only [bind, Except.bind]
      rw [checkJson_ok _ _ hr]
      rfl
  | @textEq input left right hl hr =>
      rw [infer.eq_def]
      change (do
        let l ← checkJson (canonicalSchema input) .text "textEq" "left" left.toJson
        let r ← checkJson (canonicalSchema input) .text "textEq" "right" right.toJson
        pure (⟨.boolean, .textEq l r⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ hl]
      simp only [bind, Except.bind]
      rw [checkJson_ok _ _ hr]
      rfl
  | @textAppend input left right hl hr =>
      rw [infer.eq_def]
      change (do
        let l ← checkJson (canonicalSchema input) .text "textAppend" "left" left.toJson
        let r ← checkJson (canonicalSchema input) .text "textAppend" "right" right.toJson
        pure (⟨.text, .textAppend l r⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ hl]
      simp only [bind, Except.bind]
      rw [checkJson_ok _ _ hr]
      rfl
  | @and input left right hl hr =>
      rw [infer.eq_def]
      change (do
        let l ← checkJson (canonicalSchema input) .boolean "and" "left" left.toJson
        let r ← checkJson (canonicalSchema input) .boolean "and" "right" right.toJson
        pure (⟨.boolean, .and l r⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ hl]
      simp only [bind, Except.bind]
      rw [checkJson_ok _ _ hr]
      rfl
  | @dateLe input left right hl hr =>
      rw [infer.eq_def]
      change (do
        let l ← checkJson (canonicalSchema input) .date "dateLe" "left" left.toJson
        let r ← checkJson (canonicalSchema input) .date "dateLe" "right" right.toJson
        pure (⟨.boolean, .dateLe l r⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ hl]
      simp only [bind, Except.bind]
      rw [checkJson_ok _ _ hr]
      rfl
  | @not input operand ih =>
      rw [infer.eq_def]
      change (do
        let v ← checkJson (canonicalSchema input) .boolean "not" "operand" operand.toJson
        pure (⟨.boolean, .not v⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ ih]
      rfl
  | @natToText input operand ih =>
      rw [infer.eq_def]
      change (do
        let v ← checkJson (canonicalSchema input) .natural "natToText" "operand" operand.toJson
        pure (⟨.text, .natToText v⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ ih]
      rfl
  | @ifThenElse input result condition whenTrue whenFalse hc ht hf =>
      rw [infer.eq_def]
      change (do
        let condition ← checkJson (canonicalSchema input) .boolean "ifThenElse" "condition" condition.toJson
        let ⟨result, whenTrue⟩ ← readJson (canonicalSchema input) "ifThenElse" "whenTrue" whenTrue.toJson
        let whenFalse ← checkJson (canonicalSchema input) result "ifThenElse" "whenFalse" whenFalse.toJson
        pure (⟨result, .ifThenElse condition whenTrue whenFalse⟩ : Decoded (canonicalSchema input))) = _
      rw [checkJson_ok _ _ hc]
      simp only [bind, Except.bind]
      rw [readJson_ok _ _ ht]
      simp only []
      rw [checkJson_ok _ _ hf]
      rfl
  | @all input element items body hi hb =>
      have kind : expressionKind (items.all body).toJson = .ok "all" := rfl
      have field_items : (items.all body).toJson.getObjVal? "items" = .ok items.toJson := rfl
      have field_predicate : (items.all body).toJson.getObjVal? "predicate" = .ok body.toJson := rfl
      rw [infer.eq_def, kind]
      simp [childField_ok field_items, childField_ok field_predicate, hi, hb,
        bind, Except.bind, Except.mapError, canonicalSchema, requireType, pure, Except.pure, canonicalExpr]
  | @filter input element items body hi hb =>
      have kind : expressionKind (items.filter body).toJson = .ok "filter" := rfl
      have field_items : (items.filter body).toJson.getObjVal? "items" = .ok items.toJson := rfl
      have field_predicate : (items.filter body).toJson.getObjVal? "predicate" = .ok body.toJson := rfl
      rw [infer.eq_def, kind]
      simp [childField_ok field_items, childField_ok field_predicate, hi, hb,
        bind, Except.bind, Except.mapError, canonicalSchema, requireType, pure, Except.pure, canonicalExpr]
  | @sum input element items body hi hb =>
      have kind : expressionKind (items.sum body).toJson = .ok "sum" := rfl
      have field_items : (items.sum body).toJson.getObjVal? "items" = .ok items.toJson := rfl
      have field_expression : (items.sum body).toJson.getObjVal? "expression" = .ok body.toJson := rfl
      rw [infer.eq_def, kind]
      simp [childField_ok field_items, childField_ok field_expression, hi, hb,
        bind, Except.bind, Except.mapError, canonicalSchema, requireType, pure, Except.pure, canonicalExpr]
  | @length input element items hi =>
      have kind : expressionKind (items.length).toJson = .ok "length" := rfl
      have field_items : (items.length).toJson.getObjVal? "items" = .ok items.toJson := rfl
      rw [infer.eq_def, kind]
      simp [childField_ok field_items, hi,
        bind, Except.bind, Except.mapError, canonicalSchema, pure, Except.pure, canonicalExpr]
  | @snoc input element items value hi hv =>
      have kind : expressionKind (items.snoc value).toJson = .ok "snoc" := rfl
      have field_items : (items.snoc value).toJson.getObjVal? "items" = .ok items.toJson := rfl
      have field_value : (items.snoc value).toJson.getObjVal? "value" = .ok value.toJson := rfl
      rw [infer.eq_def, kind]
      simp [childField_ok field_items, childField_ok field_value, hi, hv,
        bind, Except.bind, Except.mapError, canonicalSchema, requireType, pure, Except.pure, canonicalExpr]
  | @sortBy input element items key descending hi hk =>
      have kind : expressionKind (items.sortBy key descending).toJson = .ok "sortBy" := rfl
      have field_items : (items.sortBy key descending).toJson.getObjVal? "items" = .ok items.toJson := rfl
      have field_key : (items.sortBy key descending).toJson.getObjVal? "key" = .ok key.toJson := rfl
      have desc : (items.sortBy key descending).toJson.getObjValAs? Bool "descending" = .ok descending := by
        cases descending <;> rfl
      rw [infer.eq_def, kind]
      simp [childField_ok field_items, childField_ok field_key, hi, hk, desc,
        bind, Except.bind, Except.mapError, canonicalSchema, requireType, pure, Except.pure, canonicalExpr]
  | @sortNatBy input element items key descending hi hk =>
      have kind : expressionKind (items.sortNatBy key descending).toJson = .ok "sortNatBy" := rfl
      have field_items : (items.sortNatBy key descending).toJson.getObjVal? "items" = .ok items.toJson := rfl
      have field_key : (items.sortNatBy key descending).toJson.getObjVal? "key" = .ok key.toJson := rfl
      have desc : (items.sortNatBy key descending).toJson.getObjValAs? Bool "descending" = .ok descending := by
        cases descending <;> rfl
      rw [infer.eq_def, kind]
      simp [childField_ok field_items, childField_ok field_key, hi, hk, desc,
        bind, Except.bind, Except.mapError, canonicalSchema, requireType, pure, Except.pure, canonicalExpr]
  | @search input element items key query hi hk hq =>
      have kind : expressionKind (items.search key query).toJson = .ok "search" := rfl
      have field_items : (items.search key query).toJson.getObjVal? "items" = .ok items.toJson := rfl
      have field_key : (items.search key query).toJson.getObjVal? "key" = .ok key.toJson := rfl
      have field_query : (items.search key query).toJson.getObjVal? "query" = .ok query.toJson := rfl
      rw [infer.eq_def, kind]
      simp [childField_ok field_items, childField_ok field_key, childField_ok field_query, hi, hk, hq,
        bind, Except.bind, Except.mapError, canonicalSchema, requireType, pure, Except.pure, canonicalExpr]
  | @enumEq input labels left right hl hr =>
      have kind : expressionKind (left.enumEq right).toJson = .ok "enumEq" := rfl
      have fl : (left.enumEq right).toJson.getObjVal? "left" = .ok left.toJson := rfl
      have fr : (left.enumEq right).toJson.getObjVal? "right" = .ok right.toJson := rfl
      rw [infer.eq_def, kind]
      simp [childField_ok fl, childField_ok fr, hl, hr, canonicalSchema,
        bind, Except.bind, Except.mapError, requireType, pure, Except.pure, canonicalExpr]

  | @enumLabel input labels subject hs =>
      have kind : expressionKind subject.enumLabel.toJson = .ok "enumLabel" := rfl
      have fs : subject.enumLabel.toJson.getObjVal? "subject" = .ok subject.toJson := rfl
      have options : subject.enumLabel.toJson.getObjValAs? (List String) "options" = .ok labels.options := by
        change fromJson? (toJson labels.options) = _
        exact stringList_roundTrip _
      rw [infer.eq_def, kind]
      simp [childField_ok fs, hs, options, canonicalSchema, bind, Except.bind,
        Except.mapError, pure, Except.pure, canonicalExpr]

  | @enumCases input result labels subject bodies hs hb =>
      let rows := ((FinEnum.toList labels).map (fun i => (bodies i).toJson)).toArray
      have kind : expressionKind (subject.enumCases bodies).toJson = .ok "enumCases" := rfl
      have fs : (subject.enumCases bodies).toJson.getObjVal? "subject" = .ok subject.toJson := rfl
      have ft : (subject.enumCases bodies).toJson.getObjVal? "type" = .ok result.toJson := rfl
      have fb : (subject.enumCases bodies).toJson.getObjVal? "branches" = .ok (Json.arr rows) := by
        change Except.ok (toJson ((FinEnum.toList labels).map (fun i => (bodies i).toJson))) = _
        simp [toJson, Lean.List.toJson, Lean.Array.toJson, rows]
      have size : rows.size = labels.options.length := by
        simp [rows, Enum.options]
      rw [infer.eq_def, kind]
      simp only [childField_ok fs, bind, Except.bind, hs, Except.mapError, canonicalSchema,
        ft, schema_decode, childField_ok fb, childElements]
      simp only [Array.size_map, Array.size_attach, size, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
      rw [collectFin_ok _ (fun i => canonicalExpr (bodies ((enumIndex labels).symm i))) ?_]
      · rfl
      intro i
      have bound : i.val < rows.size := by simp [size]
      simp only [Array.getElem?_map, Array.getElem?_attach, Array.getElem?_eq_getElem bound]
      simp only [Option.pmap_some, Option.map_some]
      have row : rows[i.val] = (bodies ((enumIndex labels).symm i)).toJson := by
        simp [rows, FinEnum.toList, enumIndex]
        rfl
      rw [row, hb]
      simp [requireType]

  | @cases input result labels branches subject bodies hs hb =>
      let pairs := (FinEnum.toList labels).map (fun i => (labels.label i, (bodies i).toJson))
      have unique : (pairs.map Prod.fst).Nodup := by
        simpa [pairs, List.map_map, Function.comp_def, Enum.options] using labels.options_nodup
      have fields : checkFields (Json.mkObj pairs) labels.options = .ok () := by
        simpa only [pairs, List.map_map, Function.comp_def, Enum.options] using checkFields_mkObj unique
      have kind : expressionKind (subject.cases bodies).toJson = .ok "cases" := rfl
      have fs : (subject.cases bodies).toJson.getObjVal? "subject" = .ok subject.toJson := rfl
      have ft : (subject.cases bodies).toJson.getObjVal? "type" = .ok result.toJson := rfl
      have fb : (subject.cases bodies).toJson.getObjVal? "branches" = .ok (Json.mkObj pairs) := rfl
      rw [infer.eq_def, kind]
      simp only [childField_ok fs, bind, Except.bind, hs, Except.mapError, canonicalSchema,
        ft, schema_decode, childField_ok fb, fields]
      rw [collectFin_ok _ (fun i => canonicalExpr (bodies ((enumIndex labels).symm i))) ?_]
      · rfl
      intro i
      have label : labels.options.get i = labels.label ((enumIndex labels).symm i) := by
        simpa using enumIndex_label labels ((enumIndex labels).symm i)
      have member : (labels.label ((enumIndex labels).symm i),
          (bodies ((enumIndex labels).symm i)).toJson) ∈ pairs :=
        List.mem_map.mpr ⟨_, FinEnum.mem_toList _, rfl⟩
      have field := getObjVal_mkObj unique member
      rw [← label] at field
      rw [childField_ok field]
      simp [hb, requireType]

end Forms.Runtime.ExpressionProtocol
