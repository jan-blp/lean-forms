import Mathlib.Data.FinEnum
import Mathlib.Data.Fin.VecNotation

namespace Forms

structure Enum where
  type : Type
  [enum : FinEnum type]
  label : type → String
  label_injective : Function.Injective label

attribute [instance] Enum.enum

def Enum.options (domain : Enum) : List String :=
  (FinEnum.toList domain.type).map domain.label

inductive DataType where
  | text
  | boolean
  | natural
  | enum (domain : Enum)
  | list (element : DataType)
  | tuple {n : Nat} (children : Fin n → DataType)

abbrev DataType.denote (t : DataType) : Type :=
  match t with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .enum domain => domain.type
  | .list element => List element.denote
  | .tuple children => (i : Fin _) → DataType.denote (children i)

section Theorems

theorem Enum.options_nodup (domain : Enum) : domain.options.Nodup :=
  List.Nodup.map domain.label_injective (FinEnum.nodup_toList (α := domain.type))

end Theorems

end Forms
