import Mathlib.Data.Fin.VecNotation

namespace Forms

inductive DataType where
  | text
  | boolean
  | natural
  | tuple {n : Nat} (children : Fin n → DataType)

abbrev DataType.denote (type : DataType) : Type :=
  match type with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .tuple children => (i : Fin _) → DataType.denote (children i)

end Forms
