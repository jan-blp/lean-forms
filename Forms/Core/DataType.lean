import Mathlib.Data.Fin.VecNotation

namespace Forms

inductive DataType where
  | text
  | boolean
  | natural
  | group {n : Nat} (children : Fin n → DataType)

abbrev DataType.denote (type : DataType) : Type :=
  match type with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .group children => (i : Fin _) → DataType.denote (children i)

end Forms
