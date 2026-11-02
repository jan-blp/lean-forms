import Forms.Core.Validation

namespace Forms
open Validation

inductive RefinedDataType : (unrefined : DataType) → Type 1 where
  | base (t : DataType) : RefinedDataType t
  | refine {t : DataType}
      (refined : RefinedDataType t)
      (checked : CheckedProperty t)
      : RefinedDataType t
  | sum {tags : Enum} {constructors : tags → DataType}
      (branches : (i : tags) → RefinedDataType (constructors i))
      : RefinedDataType (.sum tags constructors)
  | list {element : DataType}
      (item : RefinedDataType element)
      : RefinedDataType (.list element)
  | record {fieldNames : Enum} {fieldTypes : fieldNames → DataType}
      (refinements : (i : fieldNames) → RefinedDataType (fieldTypes i))
      : RefinedDataType (.record fieldNames fieldTypes)

/-- A date between two inclusive bounds. Reversed bounds admit no dates. -/
def RefinedDataType.dateRange (earliest latest : Date) : RefinedDataType .date :=
  .refine (.base .date)
    { property := fun value => earliest ≤ value ∧ value ≤ latest
      checker := .when (.not (.and
        (.dateLe (.value earliest) (.project .self))
        (.dateLe (.project .self) (.value latest))))
        (.report (.value s!"Date must be between {Date.toString earliest} and {Date.toString latest}.") (.fields [[]]))
      sound := by
        intro value h
        simp [Validation.Checker.run, Validation.Checker.eval, Expr.eval, Path.get] at h
        exact ⟨of_decide_eq_true h.1, of_decide_eq_true h.2⟩ }

structure RefinedDataType.Denotation (t : DataType) where
  ValidatedValue : Type
  erase : ValidatedValue → ⟦t⟧

variable {t : DataType}

@[reducible] def RefinedDataType.denotation {t}
  (refined : RefinedDataType t)
  : RefinedDataType.Denotation t :=
  match refined with
  | .base t =>
    { ValidatedValue := ⟦t⟧
      erase := id }
  | .refine refined checked =>
    let inner := RefinedDataType.denotation refined
    { ValidatedValue := { value : inner.ValidatedValue // checked.property (inner.erase value) }
      erase := fun value => inner.erase value.val }
  | .sum branches =>
    let inner := fun i => RefinedDataType.denotation (branches i)
    { ValidatedValue := SumValue (fun i => (inner i).ValidatedValue)
      erase := fun value => { tag := value.tag, payload := (inner value.tag).erase value.payload } }
  | .list item =>
    let inner := RefinedDataType.denotation item
    { ValidatedValue := List inner.ValidatedValue
      erase := List.map inner.erase }
  | .record fields =>
    let inner := fun i => RefinedDataType.denotation (fields i)
    { ValidatedValue := (i : _) → (inner i).ValidatedValue
      erase := fun value i => (inner i).erase (value i) }

abbrev RefinedDataType.ValidatedValue (refined : RefinedDataType t) : Type :=
  (RefinedDataType.denotation refined).ValidatedValue

def RefinedDataType.erase
  (refined : RefinedDataType t)
  : RefinedDataType.ValidatedValue refined → ⟦t⟧ :=
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

def RefinedDataType.validate {t}
  (refined : RefinedDataType t)
  (draft : ⟦t⟧)
  : Option (RefinedDataType.ValidatedValue refined) :=
  match refined with
  | .sum branches =>
    Option.map (fun value => { tag := draft.tag, payload := value }) (RefinedDataType.validate (branches draft.tag) draft.payload)
  | .list item => draft.mapM (RefinedDataType.validate item)
  | .base _ => some draft
  | .record fields => sequence (fun i => RefinedDataType.validate (fields i) (draft i))
  | .refine refined checked => do
    let value ← RefinedDataType.validate refined draft
    if h : (checked.checker.run (RefinedDataType.erase refined value)).isEmpty = true then
      return { val := value, property := checked.sound _ h }
    else none

def RefinedDataType.errors {t : DataType}
  (refined : RefinedDataType t)
  (draft : ⟦t⟧)
  : List ResolvedError :=
  match refined, draft with
  | .base _, _ => []
  | .refine inner checked, draft => inner.errors draft ++ checked.checker.run draft
  | .record (fieldNames := names) fields, draft =>
      (FinEnum.toList _).flatMap fun name =>
        ((fields name).errors (draft name)).map (·.prefix (.field (names.label name)))
  | .list item, draft =>
      draft.zipIdx.flatMap fun (value, index) =>
        (item.errors value).map (·.prefix (.item index))
  | .sum (tags := tags) branches, draft =>
      ((branches draft.tag).errors draft.payload).map (·.prefix (.constructor (tags.label draft.tag)))

private theorem sequenceFin_eq_some {n : Nat} {α : Fin n → Type}
  (values : (i : Fin n) → Option (α i))
  (result : (i : Fin n) → α i)
  (h : sequenceFin values = some result)
  : ∀ i, values i = some (result i) := by
  induction n with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
      simp only [sequenceFin, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      intro i
      exact Fin.cases hhead (fun j => ih _ _ htail j) i

private theorem sequence_eq_some {ι : Type} [FinEnum ι] {α : ι → Type}
  (values : (i : ι) → Option (α i))
  (result : (i : ι) → α i)
  (h : sequence values = some result)
  : ∀ i, values i = some (result i) := by
  simp only [sequence, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨result, h, rfl⟩ := h
  intro i
  have found := sequenceFin_eq_some _ _ h (FinEnum.equiv i)
  have transport
      (j : ι)
      (same : j = i)
      (value : α j)
      (found : values j = some value)
      : values i = some (same ▸ value) := by
    cases same
    exact found
  exact transport _ (FinEnum.equiv.symm_apply_apply i) _ found

theorem RefinedDataType.erase_validate
  (refined : RefinedDataType t)
  (draft : ⟦t⟧)
  (value : refined.ValidatedValue)
  (h : refined.validate draft = some value)
  : refined.erase value = draft := by
  induction refined with
  | base => simpa [validate, erase] using h.symm
  | refine inner checked ih =>
      simp only [validate, bind, Option.bind_eq_some_iff] at h
      obtain ⟨innerValue, found, h⟩ := h
      split at h
      next valid =>
        cases h
        exact ih _ _ found
      next invalid => contradiction
  | sum branches ih =>
      simp only [validate, Option.map_eq_some_iff] at h
      obtain ⟨payload, found, rfl⟩ := h
      have same := ih draft.tag _ _ found
      cases draft
      simp_all [erase]
  | record fields ih =>
      funext i
      exact ih i _ _ (sequence_eq_some _ _ h i)
  | list item ih =>
      induction draft generalizing value with
      | nil => simpa [validate, erase] using h.symm
      | cons head tail tailIH =>
          simp only [validate, List.mapM_cons, bind, Option.bind_eq_some_iff,
            pure, Option.some.injEq] at h
          obtain ⟨headValue, hhead, tailValue, htail, rfl⟩ := h
          change item.erase headValue :: List.map item.erase tailValue = head :: tail
          rw [ih _ _ hhead]
          exact congrArg (head :: ·) (tailIH _ htail)

end Forms
