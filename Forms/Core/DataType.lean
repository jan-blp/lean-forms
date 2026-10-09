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
  | record (fields : Enum) (children : fields.type → DataType)

abbrev DataType.denote (type : DataType) : Type :=
  match type with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .enum domain => domain.type
  | .record fields children => (i : fields.type) → DataType.denote (children i)

end Forms
