import Forms.Core.Expr

namespace Forms

structure ErrorLocation (root : DataType) where
  {t : DataType}
  path : Path root t

inductive ErrorTargets (ty : DataType) where
  | global
  | fields
      (locations : List (ErrorLocation ty))
      (nonempty : locations ≠ [] := by simp)

structure Constraint (root : DataType) where
  condition : Expr root .boolean
  errorMessage : String
  errorTargets : ErrorTargets root := .global

structure ValueLocation (root : DataType) where
  {t : DataType}
  path : AffineTraversal root t

inductive LocatedTargets (root : DataType) where
  | global
  | fields
      (locations : List (ValueLocation root))
      (nonempty : locations ≠ [] := by simp)

def ErrorTargets.locate {root ty : DataType}
  (targets : ErrorTargets ty)
  (path : AffineTraversal root ty)
  : LocatedTargets root :=
  match targets with
  | .global => .global
  | .fields locations nonempty =>
      .fields (locations.map fun target =>
        { t := target.t, path := AffineTraversal.trans path target.path.toAffineTraversal }) (nonempty := by simpa)

structure ValidationError (root : DataType) where
  message : String
  targets : LocatedTargets root := .global

structure FocusedConstraint (root : DataType) where
  {t : DataType}
  constraint : Constraint t
  /-- `constraint` applies to every value traversed by `focus` -/
  focus : Traversal root t

def FocusedConstraint.errors {root : DataType}
  (rule : FocusedConstraint root)
  (value : ⟦root⟧)
  : List (ValidationError root) :=
  (rule.focus.targets value).filterMap fun found =>
    if Expr.eval rule.constraint.condition found.value then none
    else some { message := rule.constraint.errorMessage, targets := rule.constraint.errorTargets.locate found.path }

inductive RefinedDataType : (unrefined : DataType) → Type 1 where
  | base (t : DataType) : RefinedDataType t
  | refine {t : DataType}
      (refined : RefinedDataType t)
      (constraint : Constraint t)
      : RefinedDataType t
  | sum {tags : Enum} {constructors : tags → DataType}
      (branches : (i : tags) → RefinedDataType (constructors i)) : RefinedDataType (.sum tags constructors)
  | list {element : DataType}
      (item : RefinedDataType element)
      : RefinedDataType (.list element)
  | record {fieldNames : Enum} {fieldTypes : fieldNames → DataType}
      (refinements : (i : fieldNames) → RefinedDataType (fieldTypes i))
      : RefinedDataType (.record fieldNames fieldTypes)

/-- A date between two inclusive bounds. Reversed bounds admit no dates. -/
def RefinedDataType.dateRange (earliest latest : Date) : RefinedDataType .date :=
  .refine (.base .date)
    { condition := .and
        (.dateLe (.value earliest) (.project .self))
        (.dateLe (.project .self) (.value latest))
      errorMessage := s!"Date must be between {Date.toString earliest} and {Date.toString latest}."
      errorTargets := .fields [⟨.self⟩] }

structure RefinedDataType.Denotation (t : DataType) where
  ValidatedValue : Type
  erase : ValidatedValue → ⟦t⟧

variable {t : DataType}

@[reducible] def RefinedDataType.denotation {t} (refined : RefinedDataType t) : RefinedDataType.Denotation t :=
  match refined with
  | .base t =>
    { ValidatedValue := ⟦t⟧
      erase := id }
  | .refine refined constraint =>
    let inner := RefinedDataType.denotation refined
    { ValidatedValue := { value : inner.ValidatedValue // Expr.eval constraint.condition (inner.erase value) = true }
      erase := fun value => inner.erase value.val }
  | .sum branches =>
    let inner := fun i => RefinedDataType.denotation (branches i)
    { ValidatedValue := SumValue (fun i => (inner i).ValidatedValue)
      erase := fun value => ⟨value.tag, (inner value.tag).erase value.payload⟩ }
  | .list item =>
    let inner := RefinedDataType.denotation item
    { ValidatedValue := List inner.ValidatedValue
      erase := List.map inner.erase }
  | .record fields =>
    let inner := fun i => RefinedDataType.denotation (fields i)
    { ValidatedValue := (i : _) → (inner i).ValidatedValue
      erase := fun value i => (inner i).erase (value i) }

abbrev RefinedDataType.ValidatedValue (refined : RefinedDataType t) : Type := (RefinedDataType.denotation refined).ValidatedValue

def RefinedDataType.erase (refined : RefinedDataType t) : RefinedDataType.ValidatedValue refined → ⟦t⟧ :=
  (RefinedDataType.denotation refined).erase

private def sequenceFin {n : Nat} {α : Fin n → Type}
    (values : (i : Fin n) → Option (α i)) : Option ((i : Fin n) → α i) :=
  match n with
  | 0 => some (fun i => Fin.elim0 i)
  | _ + 1 => do
    let head ← values 0
    let tail ← sequenceFin (fun i => values i.succ)
    pure (Fin.cons head tail)

private def sequence {ι : Type} [FinEnum ι] {α : ι → Type}
    (values : (i : ι) → Option (α i)) : Option ((i : ι) → α i) := do
  let result ← sequenceFin (fun i => values (FinEnum.equiv.symm i))
  pure fun i => (FinEnum.equiv.symm_apply_apply i) ▸ result (FinEnum.equiv i)

def RefinedDataType.validate {t} (refined : RefinedDataType t) (draft : ⟦t⟧) : Option (RefinedDataType.ValidatedValue refined) :=
  match refined with
  | .sum branches =>
    Option.map (fun value => ⟨draft.tag, value⟩) (RefinedDataType.validate (branches draft.tag) draft.payload)
  | .list item => draft.mapM (RefinedDataType.validate item)
  | .base _ => some draft
  | .record fields => sequence (fun i => RefinedDataType.validate (fields i) (draft i))
  | .refine refined constraint => do
    let value ← RefinedDataType.validate refined draft
    if h : Expr.eval constraint.condition (RefinedDataType.erase refined value) = true then
      return ⟨value, h⟩
    else none

def RefinedDataType.constraints {t} (refined : RefinedDataType t) : List (FocusedConstraint t) :=
  match refined with
  | .sum branches =>
    (FinEnum.toList _).flatMap fun i =>
      (RefinedDataType.constraints (branches i)).map fun rule => { rule with focus := .constructor i rule.focus }
  | .list item => (RefinedDataType.constraints item).map fun rule => { rule with focus := .each rule.focus }
  | .base _ => []
  | .record fields =>
    (FinEnum.toList _).flatMap fun i =>
      (RefinedDataType.constraints (fields i)).map fun rule => { rule with focus := .field i rule.focus }
  | .refine refined constraint => RefinedDataType.constraints refined ++ [{ constraint, focus := .self }]

def RefinedDataType.errors
  (refined : RefinedDataType t)
  (draft : ⟦t⟧)
  : List (ValidationError t) :=
  (RefinedDataType.constraints refined).flatMap fun rule => rule.errors draft

section Theorems

private theorem sequenceFin_some {n : Nat} {α : Fin n → Type} (values : (i : Fin n) → α i) :
    sequenceFin (fun i => some (values i)) = some values := by
  induction n <;> simp [sequenceFin, *] <;> solve_by_elim [Subsingleton.elim, Fin.cons_self_tail]

private theorem sequence_some {ι : Type} [FinEnum ι] {α : ι → Type} (values : (i : ι) → α i) :
    sequence (fun i => some (values i)) = some values := by
  simp [sequence, sequenceFin_some]
  funext i
  have transport (j : ι) (h : j = i) : h ▸ values j = values i := by
    cases h
    rfl
  exact transport _ _

theorem RefinedDataType.validate_erase (refined : RefinedDataType t) (value : RefinedDataType.ValidatedValue refined) :
    RefinedDataType.validate refined (RefinedDataType.erase refined value) = some value := by
  induction refined with
  | sum branches ih =>
    rcases value with ⟨index, payload⟩
    change Option.map _ (RefinedDataType.validate (branches index) (RefinedDataType.erase (branches index) payload)) = _
    rw [ih]
    rfl
  | base => rfl
  | record fields ih => simp_all [validate, erase, sequence_some]
  | refine refined constraint ih =>
    simp_all [validate, erase]
    exact value.property
  | list item ih =>
    induction value with
    | nil => rfl
    | cons head tail h => simp_all [validate, erase]

private theorem sequenceFin_isSome {n : Nat} {α : Fin n → Type} (values : (i : Fin n) → Option (α i)) :
    (sequenceFin values).isSome ↔ ∀ i, (values i).isSome := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
    rw [Fin.forall_fin_succ, ← ih (fun i => values i.succ)]
    simp only [sequenceFin]
    rcases values 0 with _ | head <;> rcases sequenceFin (fun i => values i.succ) with _ | tail <;> simp

private theorem sequence_isSome {ι : Type} [FinEnum ι] {α : ι → Type} (values : (i : ι) → Option (α i)) :
    (sequence values).isSome ↔ ∀ i, (values i).isSome := by
  have : (sequence values).isSome = (sequenceFin fun i => values (FinEnum.equiv.symm i)).isSome := by
    simp only [sequence]
    rcases sequenceFin (fun i => values (FinEnum.equiv.symm i)) with _ | result <;> rfl
  rw [this, sequenceFin_isSome]
  refine ⟨fun h i => ?_, fun h i => h _⟩
  have := h (FinEnum.equiv i)
  rwa [Equiv.symm_apply_apply] at this

private theorem sequenceFin_some_eq {n : Nat} {α : Fin n → Type} {values : (i : Fin n) → Option (α i)}
    {result : (i : Fin n) → α i} (h : sequenceFin values = some result) (i : Fin n) : values i = some (result i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    simp only [sequenceFin] at h
    rcases hhead : values 0 with _ | head
    · rw [hhead] at h; cases h
    rcases htail : sequenceFin (fun i => values i.succ) with _ | tail
    · rw [hhead, htail] at h; cases h
    rw [hhead, htail] at h
    injection h with h
    subst h
    cases i using Fin.cases with
    | zero => simpa using hhead
    | succ i => simpa using ih htail i

private theorem sequence_some_eq {ι : Type} [FinEnum ι] {α : ι → Type} {values : (i : ι) → Option (α i)}
    {result : (i : ι) → α i} (h : sequence values = some result) (i : ι) : values i = some (result i) := by
  unfold sequence at h
  rcases hfound : sequenceFin (fun i => values (FinEnum.equiv.symm i)) with _ | found
  · rw [hfound] at h; cases h
  rw [hfound] at h
  injection h with h
  subst h
  have transport (j : ι) (e : j = i) (x : α j) (hx : values j = some x) : values i = some (e ▸ x) := by
    subst e; exact hx
  exact transport _ _ _ (sequenceFin_some_eq hfound (FinEnum.equiv i))

theorem Traversal.forall_targets_field {fieldNames : Enum} {fieldTypes : fieldNames → DataType} {target : DataType}
    (fieldName : fieldNames) (rest : Traversal (fieldTypes fieldName) target) (value : ⟦.record fieldNames fieldTypes⟧)
    (condition : Expr target .boolean) :
    (∀ found ∈ (Traversal.field fieldName rest).targets value, Expr.eval condition found.value = true) ↔
      ∀ found ∈ rest.targets (value fieldName), Expr.eval condition found.value = true := by
  simp only [Traversal.targets, List.forall_mem_map]

theorem Traversal.forall_targets_each {element target : DataType}
    (rest : Traversal element target) (items : ⟦.list element⟧) (condition : Expr target .boolean) :
    (∀ found ∈ (Traversal.each rest).targets items, Expr.eval condition found.value = true) ↔
      ∀ item ∈ items, ∀ found ∈ rest.targets item, Expr.eval condition found.value = true := by
  simp only [Traversal.targets, List.forall_mem_flatMap, List.forall_mem_map, Prod.forall]
  constructor
  · intro h item hitem
    obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hitem
    exact h item index (List.mem_zipIdx_iff_getElem?.mpr hindex)
  · intro h item index hitem
    exact h item (List.mem_iff_getElem?.mpr ⟨index, List.mem_zipIdx_iff_getElem?.mp hitem⟩)

theorem Traversal.forall_targets_constructor {tags : Enum} {constructors : tags → DataType} {target : DataType}
    (tag : tags) (rest : Traversal (constructors tag) target) (payload : ⟦constructors tag⟧) (condition : Expr target .boolean) :
    (∀ found ∈ (Traversal.constructor tag rest).targets (⟨tag, payload⟩ : ⟦.sum tags constructors⟧), Expr.eval condition found.value = true) ↔
      ∀ found ∈ rest.targets payload, Expr.eval condition found.value = true := by
  simp only [Traversal.targets, dite_true, List.forall_mem_map]

theorem Traversal.targets_constructor_inactive {tags : Enum} {constructors : tags → DataType} {target : DataType}
    {tag active : tags} (rest : Traversal (constructors tag) target) (payload : ⟦constructors active⟧) (h : active ≠ tag) :
    (Traversal.constructor tag rest).targets (⟨active, payload⟩ : ⟦.sum tags constructors⟧) = [] := by
  simp [Traversal.targets, h]

theorem RefinedDataType.validate_some_erase {refined : RefinedDataType t} {draft : ⟦t⟧}
    {value : RefinedDataType.ValidatedValue refined}
    (h : RefinedDataType.validate refined draft = some value) : RefinedDataType.erase refined value = draft := by
  induction refined with
  | base => simp [validate] at h; subst h; rfl
  | refine refined constraint ih =>
    simp only [validate, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨inner, hinner, hcheck⟩ := h
    split at hcheck <;> simp at hcheck
    subst hcheck
    exact ih hinner
  | sum branches ih =>
    simp only [validate, Option.map_eq_some_iff] at h
    obtain ⟨payload, hpayload, rfl⟩ := h
    have := ih draft.tag hpayload
    cases draft
    simp_all [erase]
  | list item ih =>
    induction draft generalizing value with
    | nil => simp [validate] at h; subst h; rfl
    | cons head tail ihtail =>
      simp only [validate, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, hx, xs, hxs, rfl⟩ := h
      have := ihtail (value := xs) hxs
      simp_all [erase]
      exact ih hx
  | record fields ih =>
    funext i
    exact ih i (sequence_some_eq h i)

theorem FocusedConstraint.errors_eq_nil {root : DataType} (rule : FocusedConstraint root) (value : ⟦root⟧) :
    rule.errors value = [] ↔
      ∀ found ∈ rule.focus.targets value, Expr.eval rule.constraint.condition found.value = true := by
  simp [FocusedConstraint.errors, List.filterMap_eq_nil_iff]

theorem RefinedDataType.validate_isSome_iff (refined : RefinedDataType t) (draft : ⟦t⟧) :
    (RefinedDataType.validate refined draft).isSome ↔
      ∀ rule ∈ RefinedDataType.constraints refined,
        ∀ found ∈ rule.focus.targets draft, Expr.eval rule.constraint.condition found.value = true := by
  induction refined with
  | base => simp [validate, constraints]
  | refine refined constraint ih =>
    rw [constraints]
    simp only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq, Traversal.targets, ← ih]
    simp only [validate, Option.bind_eq_bind]
    cases hinner : validate refined draft with
    | none => simp
    | some inner =>
      rw [← validate_some_erase hinner]
      simp only [Option.bind_some, Option.isSome_some, true_and]
      split <;> simp_all
  | sum branches ih =>
    rcases draft with ⟨tag, payload⟩
    simp only [validate, Option.isSome_map, ih, constraints, List.forall_mem_flatMap, List.forall_mem_map]
    constructor
    · intro h i _ rule hrule
      by_cases e : tag = i
      · subst e
        exact (Traversal.forall_targets_constructor _ _ _ _).mpr (h rule hrule)
      · simp [Traversal.targets_constructor_inactive _ _ e]
    · intro h rule hrule
      exact (Traversal.forall_targets_constructor _ _ _ _).mp (h tag (FinEnum.mem_toList _) rule hrule)
  | list item ih =>
    have mapM_isSome (items : List _) :
        (items.mapM (validate item)).isSome ↔ ∀ x ∈ items, (validate item x).isSome := by
      induction items with
      | nil => simp
      | cons head tail ihitems =>
        simp only [List.mapM_cons, List.forall_mem_cons, ← ihitems]
        cases validate item head <;> cases tail.mapM (validate item) <;> simp
    simp only [validate, mapM_isSome, ih, constraints, List.forall_mem_map, Traversal.forall_targets_each]
    exact ⟨fun h rule hrule x hx => h x hx rule hrule, fun h x hx rule hrule => h rule hrule x hx⟩
  | record fields ih =>
    simp only [validate]
    rw [sequence_isSome]
    simp only [ih, constraints, List.forall_mem_flatMap, List.forall_mem_map, Traversal.forall_targets_field]
    exact ⟨fun h i _ => h i, fun h i => h i (FinEnum.mem_toList _)⟩

/-- A draft has no validation errors exactly when it validates. -/
theorem RefinedDataType.errors_eq_nil_iff (refined : RefinedDataType t) (draft : ⟦t⟧) :
    RefinedDataType.errors refined draft = [] ↔ (RefinedDataType.validate refined draft).isSome := by
  simp [errors, List.flatMap_eq_nil_iff, FocusedConstraint.errors_eq_nil, validate_isSome_iff]

end Theorems

end Forms
