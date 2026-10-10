import Mathlib.Data.FinEnum

namespace Forms

structure Enum where
  type : Type
  [enum : FinEnum type]
  label : type → String
  label_injective : Function.Injective label := by grind [Function.Injective]

attribute [instance] Enum.enum

def Enum.options (domain : Enum) : List String :=
  (FinEnum.toList domain.type).map domain.label

inductive DataType where
  | text
  | boolean
  | natural
  | enum (domain : Enum)
  | list (element : DataType)
  | record (fields : Enum) (children : fields.type → DataType)

abbrev DataType.denote (t : DataType) : Type :=
  match t with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .enum domain => domain.type
  | .list element => List (DataType.denote element)
  | .record fields children => (i : fields.type) → DataType.denote (children i)

section Theorems

theorem Enum.options_nodup (domain : Enum) : (Enum.options domain).Nodup :=
  List.Nodup.map domain.label_injective (FinEnum.nodup_toList (α := domain.type))

end Theorems

end Forms
