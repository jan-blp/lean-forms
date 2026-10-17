import Mathlib.Data.FinEnum
import Forms.Core.Date

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
  | record (fields : Enum) (children : fields → DataType)
  | sum (tags : Enum) (constructors : tags → DataType)

structure SumValue {Tag : Type} (Payload : Tag → Type) where
  tag : Tag
  payload : Payload tag

abbrev DataType.denote (t : DataType) : Type :=
  match t with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .date => Date
  | .enum domain => domain
  | .list element => List (DataType.denote element)
  | .record fields children => (i : fields) → DataType.denote (children i)
  | .sum _ constructors => SumValue (fun i => DataType.denote (constructors i))

section Theorems

theorem Enum.options_nodup (domain : Enum) : (Enum.options domain).Nodup :=
  List.Nodup.map domain.label_injective (FinEnum.nodup_toList (α := domain))

end Theorems

end Forms
