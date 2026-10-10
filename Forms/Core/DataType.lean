import Forms.Core.Date
import Mathlib.Data.FinEnum

namespace Forms

structure Enum where
  type : Type
  [enum : FinEnum type]
  label : type → String
  label_injective : Function.Injective label := by grind [Function.Injective]

attribute [instance] Enum.enum

instance : CoeSort Enum Type where
  coe := Enum.type

def Enum.options (domain : Enum) : List String :=
  (FinEnum.toList domain).map domain.label

inductive DataType where
  | text
  | boolean
  | natural
  | date
  | enum (domain : Enum)
  | list (element : DataType)
  | record (fieldNames : Enum) (fieldTypes : fieldNames → DataType)

abbrev DataType.denote (t : DataType) : Type :=
  match t with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .date => Date
  | .enum domain => domain
  | .list element => List (DataType.denote element)
  | .record fieldNames fieldTypes => (i : fieldNames) → DataType.denote (fieldTypes i)

section Theorems

theorem Enum.options_nodup (domain : Enum) : (Enum.options domain).Nodup :=
  List.Nodup.map domain.label_injective (FinEnum.nodup_toList (α := domain))

end Theorems

end Forms
