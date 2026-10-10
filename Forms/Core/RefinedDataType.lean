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
  { condition := constraint.condition.weaken path
    errorMessage := constraint.errorMessage
    errorLocation := constraint.errorLocation.map fun target => ⟨path.trans target.path⟩ }

end

inductive RefinedDataType : DataType → Type 1 where
  | list {element : DataType} (item : RefinedDataType element) : RefinedDataType (.list element)
  | base (t : DataType) : RefinedDataType t
  | group {n : Nat} {children : Fin n → DataType}
      (fields : (i : Fin n) → RefinedDataType (children i))
      : RefinedDataType (.group children)
  | refine {t : DataType} (refined : RefinedDataType t) (constraint : Constraint t) : RefinedDataType t

structure RefinedDataType.Denotation (t : DataType) where
  Value : Type
  erase : Value → DataType.denote t

variable {t : DataType}

@[reducible] def RefinedDataType.denotation {t} : RefinedDataType t → RefinedDataType.Denotation t
  | .list item => ⟨List item.denotation.Value, List.map item.denotation.erase⟩
  | .base t => ⟨DataType.denote t, id⟩
  | .group fields =>
    ⟨(i : Fin _) → (fields i).denotation.Value,
      fun value i => (fields i).denotation.erase (value i)⟩
  | .refine refined constraint =>
    let inner := refined.denotation
    ⟨{ value : inner.Value // Expr.eval constraint.condition (inner.erase value) = true },
      fun value => inner.erase value.val⟩

abbrev RefinedDataType.denote (refined : RefinedDataType t) : Type := refined.denotation.Value

def RefinedDataType.erase (refined : RefinedDataType t) : refined.denote → DataType.denote t :=
  refined.denotation.erase

private def sequence {n : Nat} {α : Fin n → Type}
    (values : (i : Fin n) → Option (α i)) : Option ((i : Fin n) → α i) :=
  match n with
  | 0 => some (fun i => Fin.elim0 i)
  | _ + 1 => do
    let head ← values 0
    let tail ← sequence (fun i => values i.succ)
    pure (Fin.cons head tail)

def RefinedDataType.validate {t} (refined : RefinedDataType t) (draft : DataType.denote t) : Option refined.denote :=
  match refined with
  | .list item => draft.mapM item.validate
  | .base _ => some draft
  | .group fields => sequence (fun i => (fields i).validate (draft i))
  | .refine refined constraint => do
    let value ← refined.validate draft
    if h : Expr.eval constraint.condition (refined.erase value) = true then
      return ⟨value, h⟩
    else none

def RefinedDataType.constraints {t} : RefinedDataType t → List (Constraint t)
  | .list item => item.constraints.map fun constraint =>
      { condition := .all (.project .here) constraint.condition
        errorMessage := constraint.errorMessage
        errorLocation := some ⟨.here⟩ }
  | .base _ => []
  | .group fields =>
    (List.finRange _).flatMap fun i =>
      (fields i).constraints.map (Constraint.weaken (.child i .here))
  | .refine refined constraint => refined.constraints ++ [constraint]

def RefinedDataType.errors (refined : RefinedDataType t) (draft : DataType.denote t) : List (Constraint t) :=
  refined.constraints.filter fun constraint => !(Expr.eval constraint.condition draft)

section Theorems

private theorem sequence_some {n : Nat} {α : Fin n → Type} (values : (i : Fin n) → α i) :
    sequence (fun i => some (values i)) = some values := by
  induction n <;> simp [sequence, *] <;> solve_by_elim [Subsingleton.elim, Fin.cons_self_tail]

theorem RefinedDataType.validate_erase (refined : RefinedDataType t) (value : refined.denote) :
    refined.validate (refined.erase value) = some value := by
  induction refined with
  | base => rfl
  | group fields ih => simp_all [validate, erase, sequence_some]
  | refine refined constraint ih =>
    simp_all [validate, erase]
    exact value.property
  | list item ih =>
    induction value with
    | nil => rfl
    | cons head tail h => simp_all [validate, erase]

end Theorems

end Forms
