import Forms.Core.DataType

namespace Forms

inductive Delta : DataType → Type 1 where
  | replace {t : DataType} (value : DataType.denote t) : Delta t
  | field {fieldNames : Enum} {types : fieldNames → DataType}
      (field : fieldNames) (delta : Delta (types field)) : Delta (.record fieldNames types)

def Delta.apply {t : DataType} (delta : Delta t) (value : DataType.denote t) : DataType.denote t :=
  match delta with
  | .replace value => value
  | .field fieldName delta => Function.update value fieldName (Delta.apply delta (value fieldName))

section Theorems

variable {t : DataType} (x y : DataType.denote t) (d : Delta t)

@[simp] theorem Delta.apply_replace
  : Delta.apply (.replace x) y = x
  := rfl

theorem Delta.apply_replace_apply
  : Delta.apply (.replace x) (Delta.apply d y) = Delta.apply (.replace x) y
  := rfl

section Record

variable {fieldNames : Enum} {types : fieldNames → DataType}
variable (value : DataType.denote (.record fieldNames types))
variable (field other : fieldNames) (delta : Delta (types field))

@[simp] theorem Delta.apply_field_same
  : Delta.apply (.field field delta) value field = Delta.apply delta (value field)
  := by simp [Delta.apply]

@[simp] theorem Delta.apply_field_other (h : other ≠ field)
  : Delta.apply (.field field delta) value other = value other
  := by simp [Delta.apply, h]

end Record

end Theorems

end Forms
