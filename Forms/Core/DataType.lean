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
  | record (fields : Enum) (children : fields → DataType)

abbrev DataType.denote (type : DataType) : Type :=
  match type with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .date => Date
  | .enum domain => domain
  | .record fields children => (i : fields) → DataType.denote (children i)

end Forms
