import Forms.Core.RefinedDataType

namespace Forms
open Validation
open private sequenceFin sequence from Forms.Core.RefinedDataType

variable {t : DataType}

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
  | serverRefine inner checked ih =>
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

private theorem sequenceFin_some {n : Nat} {α : Fin n → Type}
  (values : (i : Fin n) → α i)
  : sequenceFin (fun i => some (values i)) = some values := by
  induction n <;> simp [sequenceFin, *] <;> solve_by_elim [Subsingleton.elim, Fin.cons_self_tail]

private theorem sequence_some {ι : Type} [FinEnum ι] {α : ι → Type}
  (values : (i : ι) → α i)
  : sequence (fun i => some (values i)) = some values := by
  simp [sequence, sequenceFin_some]
  funext i
  have transport (j : ι) (h : j = i) : h ▸ values j = values i := by
    cases h
    rfl
  exact transport _ _

private theorem sequenceFin_isSome {n : Nat} {α : Fin n → Type}
  (values : (i : Fin n) → Option (α i))
  : (sequenceFin values).isSome ↔ ∀ i, (values i).isSome := by
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [Fin.forall_fin_succ, ← ih (fun i => values i.succ)]
      simp only [sequenceFin]
      rcases values 0 with _ | head <;> rcases sequenceFin (fun i => values i.succ) with _ | tail <;> simp

private theorem sequence_isSome {ι : Type} [FinEnum ι] {α : ι → Type}
  (values : (i : ι) → Option (α i))
  : (sequence values).isSome ↔ ∀ i, (values i).isSome := by
  have : (sequence values).isSome = (sequenceFin fun i => values (FinEnum.equiv.symm i)).isSome := by
    simp only [sequence]
    rcases sequenceFin (fun i => values (FinEnum.equiv.symm i)) with _ | result <;> rfl
  rw [this, sequenceFin_isSome]
  refine ⟨fun h i => ?_, fun h i => h _⟩
  have := h (FinEnum.equiv i)
  rwa [Equiv.symm_apply_apply] at this

/-- Complete checkers accept every validated value. -/
theorem RefinedDataType.validate_erase
  (refined : RefinedDataType t)
  (complete : refined.Complete)
  (value : refined.ValidatedValue)
  : refined.validate (refined.erase value) = some value := by
  induction refined with
  | base => rfl
  | refine inner checked ih =>
      have accepted := complete.2 _ value.property
      simp_all [validate, erase, Complete]
  | serverRefine inner checked ih =>
      have accepted := value.property
      simp_all [validate, erase, Complete]
      split
      next => rfl
      next _ rejected _ _ _ => exact False.elim (rejected accepted)
  | sum branches ih =>
      rcases value with ⟨tag, payload⟩
      change Option.map _ ((branches tag).validate ((branches tag).erase payload)) = _
      rw [ih tag (complete tag)]
      rfl
  | record fields ih =>
      simp_all [validate, erase, Complete, sequence_some]
  | list item ih =>
      induction value with
      | nil => rfl
      | cons head tail tailIH => simp_all [validate, erase, Complete]

/-- No errors iff valid. -/
theorem RefinedDataType.errors_eq_nil_iff
  (refined : RefinedDataType t)
  (draft : ⟦t⟧)
  : refined.errors draft = [] ↔ (refined.validate draft).isSome := by
  induction refined with
  | base => simp [errors, validate]
  | refine inner checked ih =>
      simp only [errors, List.append_eq_nil_iff, ih, validate, bind]
      cases found : inner.validate draft with
      | none => simp
      | some innerValue =>
          rw [← erase_validate inner draft innerValue found]
          simp only [Option.isSome_some, true_and, Option.bind_some]
          split
          next valid => simpa [pure] using List.isEmpty_iff.mp valid
          next invalid => simpa using invalid
  | serverRefine inner checked ih =>
      simp only [errors, ServerProperty.errors, List.append_eq_nil_iff, ih, validate, bind]
      cases found : inner.validate draft with
      | none => simp
      | some innerValue =>
          simp only [Option.isSome_some, true_and, Option.bind_some]
          rw [← erase_validate inner draft innerValue found]
          split <;> simp_all
  | sum branches ih =>
      rcases draft with ⟨tag, payload⟩
      simp [errors, validate, ih, ResolvedError.mapLocations]
  | record fields ih =>
      simp only [errors, validate, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, ih]
      rw [sequence_isSome]
      exact ⟨fun h i => h i (FinEnum.mem_toList _), fun h i _ => h i⟩
  | list item ih =>
      have mapM_isSome (items : List _)
          : (items.mapM item.validate).isSome ↔ ∀ x ∈ items, (item.validate x).isSome := by
        induction items with
        | nil => simp
        | cons head tail ihItems =>
            simp only [List.mapM_cons, List.forall_mem_cons, ← ihItems]
            cases item.validate head <;> cases tail.mapM item.validate <;> simp
      simp only [errors, validate, mapM_isSome, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, ← ih, Prod.forall]
      constructor
      · intro h x hx
        obtain ⟨index, hindex⟩ := List.mem_iff_getElem?.mp hx
        exact h x index (List.mem_zipIdx_iff_getElem?.mpr hindex)
      · intro h x index hx
        exact h x (List.mem_iff_getElem?.mpr ⟨index, List.mem_zipIdx_iff_getElem?.mp hx⟩)

end Forms
