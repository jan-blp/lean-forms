module

public import Forms.Runtime.ExpressionProtocol.Program
public import Mathlib.Logic.Equiv.List
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace Forms.Runtime.ExpressionProtocol
open Lean

set_option backward.isDefEq.respectTransparency false

/-- The wire index of an application-defined label. -/
def enumIndex (domain : Enum) : domain ≃ Fin (Enum.options domain).length :=
  FinEnum.equiv.trans (finCongr (by simp [Enum.options, FinEnum.toList]))

/-- Replace application-defined label types with the finite indices used on the wire. -/
abbrev canonicalSchema : DataType → Schema
  | .text => .text
  | .boolean => .boolean
  | .natural => .natural
  | .date => .date
  | .list element => .list (canonicalSchema element)
  | .enum labels => .enum labels.options labels.options_nodup
  | .record labels fields => .record labels.options labels.options_nodup
      (fun i => canonicalSchema (fields ((enumIndex labels).symm i)))
  | .sum labels branches => .sum labels.options labels.options_nodup
      (fun i => canonicalSchema (branches ((enumIndex labels).symm i)))

def sumValueEquiv {α : Type} (types : α → Type) : SumValue types ≃ Sigma types where
  toFun := fun v => ⟨v.tag, v.payload⟩
  invFun := fun v => ⟨v.1, v.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The wire representation is isomorphic to the application's value type. -/
def canonicalEquiv (t : DataType) : ⟦t⟧ ≃ ⟦(canonicalSchema t).dataType⟧ :=
  match t with
  | .text | .boolean | .natural | .date => Equiv.refl _
  | .enum labels => enumIndex labels
  | .list element => Equiv.listEquivOfEquiv (canonicalEquiv element)
  | .record labels fields =>
      (Equiv.piCongrRight (fun i => canonicalEquiv (fields i))).trans
        (Equiv.piCongrLeft' (fun i => ⟦(canonicalSchema (fields i)).dataType⟧) (enumIndex labels))
  | .sum labels branches =>
      (sumValueEquiv (fun i => ⟦branches i⟧)).trans
        ((Equiv.sigmaCongr (enumIndex labels) (fun i => by
          simpa using canonicalEquiv (branches i))).trans (sumValueEquiv _).symm)
termination_by structural t

@[simp] theorem enumIndex_label (labels : Enum) (i : labels) :
    labels.options.get (enumIndex labels i) = labels.label i := by
  simp [Enum.options, FinEnum.toList, enumIndex, List.get_eq_getElem]

theorem toList_length (labels : Enum) : (FinEnum.toList labels).length = labels.options.length := by
  simp [Enum.options]

theorem toList_getElem (labels : Enum) (i : Fin labels.options.length) (h) :
    (FinEnum.toList labels)[i.val]'h = (enumIndex labels).symm i := by
  simp [FinEnum.toList, enumIndex]; rfl

@[simp] theorem canonicalEquiv_list (element : DataType) (xs : List ⟦element⟧) :
    canonicalEquiv (.list element) xs = xs.map (canonicalEquiv element) := rfl

@[simp] theorem canonicalEquiv_record (labels : Enum) (fields : labels → DataType)
    (value : ⟦.record labels fields⟧) (i : Fin labels.options.length) :
    canonicalEquiv (.record labels fields) value i =
      canonicalEquiv (fields ((enumIndex labels).symm i)) (value ((enumIndex labels).symm i)) := rfl

def canonicalPath {input result : DataType} (path : Path input result) :
    Path (canonicalSchema input).dataType (canonicalSchema result).dataType :=
  match path with
  | .self => .self
  | .field (fieldNames := labels) i rest =>
      .field (enumIndex labels i) (by simpa using canonicalPath rest)

theorem path_get_reindex {α : Type} (types : α → DataType) {a b : α}
    (h : a = b) {result : DataType} (path : Path (types b) result)
    (values : (i : α) → ⟦types i⟧) :
    ((congrArg types h).symm ▸ path).get (values a) = path.get (values b) := by
  cases h
  rfl

theorem canonicalPath_get {input result : DataType} (path : Path input result)
    (value : ⟦input⟧) :
    (canonicalPath path).get (canonicalEquiv input value) = canonicalEquiv result (path.get value) := by
  induction path with
  | self => rfl
  | @field labels fields result i rest ih =>
      simp only [canonicalPath, Path.get]
      rw [canonicalEquiv_record]
      simpa only [Eq.mpr, eqRec_eq_cast] using (path_get_reindex (fun i => (canonicalSchema (fields i)).dataType)
        ((enumIndex labels).symm_apply_apply i) (canonicalPath rest)
        (fun j => canonicalEquiv (fields j) (value j))).trans (ih (value i))

@[simp] theorem canonicalSchema_iteration (outer element : DataType) :
    canonicalSchema (Validation.IterationContext outer element) =
      iterationSchema (canonicalSchema outer) (canonicalSchema element) := by
  change Schema.record _ _ _ = Schema.record _ _ _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_cast_eval {a b : Schema} {result : DataType} (h : a = b)
    (program : Program a.dataType result) (value : ⟦a.dataType⟧) :
    (cast (congrArg (fun s => Program s.dataType result) h) program).eval
      (cast (congrArg (fun (s : Schema) => DataType.denote s.dataType) h) value) = program.eval value := by
  cases h
  rfl

theorem cast_record_apply {names : List String} {unique : names.Nodup}
    {fields other : Fin names.length → Schema}
    (h : Schema.record names unique fields = Schema.record names unique other)
    (value : ⟦(Schema.record names unique fields).dataType⟧) (i : Fin names.length) :
    (cast (congrArg (fun (s : Schema) => DataType.denote s.dataType) h) value) i =
      cast (congrArg (fun (s : Schema) => DataType.denote s.dataType)
        (congrFun (by injection h) i)) (value i) := by
  have same : fields = other := by injection h
  subst other
  rfl

theorem canonicalIterationValue (outer element : DataType)
    (value : ⟦outer⟧) (item : ⟦element⟧) (index : Nat) :
    cast (congrArg (fun (s : Schema) => DataType.denote s.dataType) (canonicalSchema_iteration outer element))
      (canonicalEquiv (Validation.IterationContext outer element)
        (fun | .outer => value | .item => item | .index => index)) =
      iterationValue (canonicalEquiv outer value) (canonicalEquiv element item) index := by
  funext i
  rw [cast_record_apply (canonicalSchema_iteration outer element)]
  fin_cases i <;> rfl

def canonicalExpr {input result : DataType} (expression : Forms.Expr input result) :
    Program (canonicalSchema input).dataType (canonicalSchema result).dataType :=
  match expression with
  | .value v => .value (canonicalEquiv result v)
  | .project path => .project (canonicalPath path)
  | .all (outer := outer) (element := element) items predicate context =>
      .all (outer := canonicalSchema outer) (element := canonicalSchema element)
        (canonicalExpr items) (cast (congrArg (fun schema => Program schema.dataType .boolean)
          (canonicalSchema_iteration outer element)) (canonicalExpr predicate))
        (canonicalPath context)
  | .cases (tags := labels) subject branches =>
      .cases (canonicalExpr subject) (fun i => canonicalExpr (branches ((enumIndex labels).symm i)))
  | .sum items body => .sum (canonicalExpr items) (canonicalExpr body)
  | .filter items predicate => .filter (canonicalExpr items) (canonicalExpr predicate)
  | .sortBy items key descending => .sortBy (canonicalExpr items) (canonicalExpr key) descending
  | .search items key query => .search (canonicalExpr items) (canonicalExpr key) (canonicalExpr query)
  | .sortNatBy items key descending => .sortNatBy (canonicalExpr items) (canonicalExpr key) descending
  | .snoc items v => .snoc (canonicalExpr items) (canonicalExpr v)
  | .length items => .length (canonicalExpr items)
  | .enumCases (domain := labels) subject branches =>
      .enumCases (canonicalExpr subject) (fun i => canonicalExpr (branches ((enumIndex labels).symm i)))
  | .enumEq l r => .enumEq (canonicalExpr l) (canonicalExpr r)
  | .enumLabel subject => .enumLabel (canonicalExpr subject)
  | .ifThenElse c t f => .ifThenElse (canonicalExpr c) (canonicalExpr t) (canonicalExpr f)
  | .natToText v => .natToText (canonicalExpr v)
  | .textEq l r => .textEq (canonicalExpr l) (canonicalExpr r)
  | .textAppend l r => .textAppend (canonicalExpr l) (canonicalExpr r)
  | .natAdd l r => .natAdd (canonicalExpr l) (canonicalExpr r)
  | .natSub l r => .natSub (canonicalExpr l) (canonicalExpr r)
  | .natMul l r => .natMul (canonicalExpr l) (canonicalExpr r)
  | .not v => .not (canonicalExpr v)
  | .and l r => .and (canonicalExpr l) (canonicalExpr r)
  | .dateLe l r => .dateLe (canonicalExpr l) (canonicalExpr r)
  | .natLe l r => .natLe (canonicalExpr l) (canonicalExpr r)

@[simp] theorem canonicalEquiv_natural (v : Nat) : canonicalEquiv .natural v = v := rfl
@[simp] theorem canonicalEquiv_text (v : String) : canonicalEquiv .text v = v := rfl
@[simp] theorem canonicalEquiv_boolean (v : Bool) : canonicalEquiv .boolean v = v := rfl
@[simp] theorem canonicalEquiv_date (v : Date) : canonicalEquiv .date v = v := rfl
@[simp] theorem canonicalEquiv_enum (labels : Enum) (v : labels) :
    canonicalEquiv (.enum labels) v = enumIndex labels v := rfl

theorem reindex_equiv_apply {α A B : Type} (types : α → Type)
    (f : (a : α) → types a → B) {a b : α} (h : a = b)
    (e : A ≃ types b) (v : A) :
    f a ((cast (congrArg (fun x => A ≃ types x) h.symm) e) v) = f b (e v) := by
  cases h
  rfl

attribute [local simp] Program.value Program.project Program.cases Program.sum Program.filter Program.sortBy Program.search Program.sortNatBy Program.snoc Program.length Program.enumCases Program.enumEq Program.enumLabel Program.ifThenElse Program.natToText Program.textEq Program.textAppend Program.natAdd Program.natSub Program.natMul Program.not Program.and Program.dateLe Program.natLe Program.all

theorem canonicalExpr_eval {input result : DataType} (expression : Forms.Expr input result)
    (value : ⟦input⟧) :
    (canonicalExpr expression).eval (canonicalEquiv input value) =
      canonicalEquiv result (expression.eval value) := by
  induction expression with
  | @all input outer element items predicate context hi hp =>
      simp only [canonicalExpr, Program.all, Forms.Expr.eval, hi, canonicalPath_get]
      change ((items.eval value).map (canonicalEquiv element)).zipIdx.all _ =
        (items.eval value).zipIdx.all _
      rw [← List.map_zipIdx, List.all_map]
      apply congrArg (List.all (items.eval value).zipIdx)
      funext pair
      rcases pair with ⟨item, index⟩
      dsimp
      rw [← canonicalIterationValue, program_cast_eval (canonicalSchema_iteration outer element)]
      exact hp _
  | project path => exact canonicalPath_get path value
  | @sortBy i e items key descending hi hk | @sortNatBy i e items key descending hi hk =>
      simp_all [canonicalExpr, Forms.Expr.eval, canonicalEquiv, Equiv.listEquivOfEquiv]
      exact (List.map_mergeSort (by intros; simp [hk])).symm
  | @search i e items key query hi hk hq =>
      simp_all [canonicalExpr, Forms.Expr.eval, canonicalEquiv, Equiv.listEquivOfEquiv,
        List.filter_map, Function.comp_def]
      rw [hq]
  | @enumLabel i labels subject ih =>
      simpa [canonicalExpr, Forms.Expr.eval, canonicalEquiv, ih, List.get_eq_getElem]
        using enumIndex_label labels (subject.eval value)
  | @cases i r labels branches subject bodies hi hb =>
      simp only [canonicalExpr, Forms.Expr.eval, Program.cases]
      rw [hi]
      dsimp [canonicalEquiv, sumValueEquiv, Equiv.sigmaCongr, Equiv.sigmaCongrLeft, Equiv.sigmaCongrRight]
      exact (reindex_equiv_apply (fun j => ⟦(canonicalSchema (branches j)).dataType⟧)
        (fun j => (canonicalExpr (bodies j)).eval)
        ((enumIndex labels).symm_apply_apply (subject.eval value).tag)
        (canonicalEquiv (branches (subject.eval value).tag)) (subject.eval value).payload).trans
        (hb _ _)
  | _ => simp_all [canonicalExpr, Forms.Expr.eval, canonicalEquiv, Equiv.listEquivOfEquiv,
      List.filter_map, Function.comp_def, apply_ite]

theorem map_finRange_cast {α : Type} {m n : Nat} (h : m = n) (f : Fin n → α) :
    (List.finRange m).map (fun i => f (Fin.cast h i)) = (List.finRange n).map f := by
  subst n
  rfl

theorem enumIndex_toList (labels : Enum) :
    (@FinEnum.toList _ (domain labels.options labels.options_nodup).enum).map (enumIndex labels).symm =
      FinEnum.toList labels := by
  simp [FinEnum.card, FinEnum.equiv, FinEnum.toList, enumIndex, domain, Enum.options, Function.comp_def]
  exact map_finRange_cast _ _

theorem canonicalValue_toJson (type : DataType) (value : ⟦type⟧) :
    JsonProtocol.valueToJson (canonicalEquiv type value) = JsonProtocol.valueToJson value := by
  induction type with
  | text | boolean | natural | date => rfl
  | enum labels =>
      simp [FinEnum.card, FinEnum.equiv, canonicalEquiv, canonicalSchema, Schema.dataType, JsonProtocol.valueToJson, enumIndex, domain]
  | list element ih =>
      simp [canonicalEquiv, Equiv.listEquivOfEquiv, JsonProtocol.valueToJson,
        List.map_map, Function.comp_def, ih]
  | record labels fields ih =>
      change Json.mkObj ((@FinEnum.toList _ (domain labels.options labels.options_nodup).enum).map
        (fun j => (labels.options.get j, JsonProtocol.valueToJson
          (canonicalEquiv (fields ((enumIndex labels).symm j)) (value ((enumIndex labels).symm j)))))) = _
      simp_rw [ih]
      have label (j : Fin labels.options.length) :
          labels.options.get j = labels.label ((enumIndex labels).symm j) := by
        simpa using enumIndex_label labels ((enumIndex labels).symm j)
      simp_rw [label]
      exact congrArg Json.mkObj (by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map (fun i => (labels.label i, JsonProtocol.valueToJson (value i))))
            (enumIndex_toList labels))
  | sum labels branches ih =>
      dsimp [canonicalEquiv, sumValueEquiv, Equiv.sigmaCongr, Equiv.sigmaCongrLeft,
        Equiv.sigmaCongrRight, JsonProtocol.valueToJson]
      have payload := reindex_equiv_apply
        (fun j => ⟦(canonicalSchema (branches j)).dataType⟧)
        (fun j => JsonProtocol.valueToJson (t := (canonicalSchema (branches j)).dataType))
        ((enumIndex labels).symm_apply_apply value.tag)
        (canonicalEquiv (branches value.tag)) value.payload
      rw [payload, ih]
      congr 3
      exact congrArg toJson (enumIndex_label labels value.tag)

theorem cast_equiv_apply {A B C : Type} (h : B = C) (e : A ≃ B) (v : A) :
    (cast (congrArg (fun t => A ≃ t) h) e) v = cast h (e v) := by
  cases h
  rfl

theorem canonicalEquiv_sum (labels : Enum) (branches : labels → DataType)
    (value : ⟦.sum labels branches⟧) :
    canonicalEquiv (.sum labels branches) value =
      ⟨enumIndex labels value.tag,
        cast (congrArg (fun i => DataType.denote (canonicalSchema (branches i)).dataType)
          ((enumIndex labels).symm_apply_apply value.tag)).symm
          (canonicalEquiv (branches value.tag) value.payload)⟩ := by
  dsimp [canonicalEquiv, sumValueEquiv, Equiv.sigmaCongr, Equiv.sigmaCongrLeft, Equiv.sigmaCongrRight]
  congr 1
  apply cast_equiv_apply

end Forms.Runtime.ExpressionProtocol
