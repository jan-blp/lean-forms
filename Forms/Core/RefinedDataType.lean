import Forms.Core.Expr

namespace Forms

structure ErrorLocation (root : DataType) where
  {t : DataType}
  path : Path root t

structure Constraint (root : DataType) where
  condition : Expr root .boolean
  errorMessage : String
  errorLocation : Option (ErrorLocation root) := none

section

variable {outer root : DataType}

def Constraint.weaken (path : Path outer root) (constraint : Constraint root) : Constraint outer :=
  { condition := Expr.weaken path constraint.condition
    errorMessage := constraint.errorMessage
    errorLocation := constraint.errorLocation.map fun target => ⟨Path.trans path target.path⟩ }

end

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
      errorLocation := some ⟨.self⟩ }

structure RefinedDataType.Denotation (t : DataType) where
  ValidatedValue : Type
  erase : ValidatedValue → DataType.denote t

variable {t : DataType}

@[reducible] def RefinedDataType.denotation {t} (refined : RefinedDataType t) : RefinedDataType.Denotation t :=
  match refined with
  | .base t =>
    { ValidatedValue := DataType.denote t
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

def RefinedDataType.erase (refined : RefinedDataType t) : RefinedDataType.ValidatedValue refined → DataType.denote t :=
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

def RefinedDataType.validate {t} (refined : RefinedDataType t) (draft : DataType.denote t) : Option (RefinedDataType.ValidatedValue refined) :=
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

def RefinedDataType.constraints {t} (refined : RefinedDataType t) : List (Constraint t) :=
  match refined with
  | .sum branches =>
    (FinEnum.toList _).flatMap fun i =>
      (RefinedDataType.constraints (branches i)).map fun constraint =>
        { condition := .cases (.project .self) fun j =>
            if h : j = i then h.symm ▸ constraint.condition else .value true
          errorMessage := constraint.errorMessage
          errorLocation := some ⟨.self⟩ }
  | .list item => (RefinedDataType.constraints item).map fun constraint =>
      { condition := .all (.project .self) constraint.condition
        errorMessage := constraint.errorMessage
        errorLocation := some ⟨.self⟩ }
  | .base _ => []
  | .record fields =>
    (FinEnum.toList _).flatMap fun i =>
      (RefinedDataType.constraints (fields i)).map (Constraint.weaken (.field i .self))
  | .refine refined constraint => RefinedDataType.constraints refined ++ [constraint]

def RefinedDataType.errors (refined : RefinedDataType t) (draft : DataType.denote t) : List (Constraint t) :=
  (RefinedDataType.constraints refined).filter fun constraint => !(Expr.eval constraint.condition draft)

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

end Theorems

end Forms
