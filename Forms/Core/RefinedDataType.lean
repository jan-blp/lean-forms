module

public import Forms.Core.Validation

@[expose] public section

namespace Forms
open Validation

inductive RefinedDataType : (unrefined : DataType) → Type 1 where
  | base (t : DataType) : RefinedDataType t
  | refine {t : DataType}
      (refined : RefinedDataType t)
      (checked : CheckedProperty t)
      : RefinedDataType t
  | serverRefine {t : DataType}
      (refined : RefinedDataType t)
      (checked : ServerProperty t)
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
    (.require (fun value => earliest ≤ value ∧ value ≤ latest)
      (.and (.dateLe (.value earliest) (.project .self)) (.dateLe (.project .self) (.value latest)))
      (.value s!"Date must be between {Date.toString earliest} and {Date.toString latest}.")
      (.locations [.self]))

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
  | .serverRefine refined checked =>
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

def sequenceFin {n : Nat} {α : Fin n → Type}
    (values : (i : Fin n) → Option (α i)) : Option ((i : Fin n) → α i) :=
  match n with
  | 0 => some (fun i => Fin.elim0 i)
  | _ + 1 => do
    let head ← values 0
    let tail ← sequenceFin (fun i => values i.succ)
    pure (Fin.cons head tail)

def sequence {ι : Type} [FinEnum ι] {α : ι → Type}
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

  | .serverRefine refined checked => do
    let value ← RefinedDataType.validate refined draft
    match checked.check (RefinedDataType.erase refined value) with
    | .valid h => return ⟨value, h⟩
    | .invalid .. => none

def RefinedDataType.errors {t : DataType}
  (refined : RefinedDataType t)
  (draft : ⟦t⟧)
  : List (ResolvedError t) :=
  match refined, draft with
  | .base _, _ => []
  | .refine inner checked, draft => inner.errors draft ++ checked.checker.run draft
  | .serverRefine inner checked, draft => inner.errors draft ++ checked.errors draft
  | .record fields, draft =>
      (FinEnum.toList _).flatMap fun name =>
        ((fields name).errors (draft name)).map (·.mapLocations (.field name))
  | .list item, draft =>
      draft.zipIdx.flatMap fun (value, index) =>
        (item.errors value).map (·.mapLocations (.item index))
  | .sum branches, draft =>
      ((branches draft.tag).errors draft.payload).map (·.mapLocations (.constructor draft.tag))

/-- All checkers are complete. -/
def RefinedDataType.Complete {t} (refined : RefinedDataType t) : Prop :=
  match refined with
  | .base _ => True
  | .refine inner checked => inner.Complete ∧ checked.Complete
  | .serverRefine inner _ => inner.Complete
  | .sum branches => ∀ i, (branches i).Complete
  | .list item => item.Complete
  | .record fields => ∀ i, (fields i).Complete

end Forms
