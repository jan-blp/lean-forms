import Mathlib.Data.FinEnum
import Mathlib.Data.Fin.VecNotation

namespace Forms

structure Choice where
  type : Type
  [enum : FinEnum type]
  label : type → String
  label_injective : Function.Injective label

attribute [instance] Choice.enum

def Choice.options (choice : Choice) : List String :=
  (FinEnum.toList choice.type).map choice.label

inductive DataType where
  | text
  | boolean
  | natural
  | choice (domain : Choice)
  | list (element : DataType)
  | group {n : Nat} (children : Fin n → DataType)

abbrev DataType.denote (t : DataType) : Type :=
  match t with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .choice domain => domain.type
  | .list element => List element.denote
  | .group children => (i : Fin _) → DataType.denote (children i)

section Theorems

theorem Choice.options_nodup (choice : Choice) : choice.options.Nodup :=
  List.Nodup.map choice.label_injective (FinEnum.nodup_toList (α := choice.type))

end Theorems

end Forms
