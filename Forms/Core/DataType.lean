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

theorem Enum.options_nodup (domain : Enum) : domain.options.Nodup :=
  List.Nodup.map domain.label_injective (FinEnum.nodup_toList (α := domain.type))

inductive DataType where
  | text
  | boolean
  | natural
  | enum (domain : Enum)
  | tuple {n : Nat} (children : Fin n → DataType)

abbrev DataType.denote (type : DataType) : Type :=
  match type with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .enum domain => domain.type
  | .tuple children => (i : Fin _) → DataType.denote (children i)

end Forms
