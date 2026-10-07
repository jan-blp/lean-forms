namespace Forms

inductive DataType where
  | text
  | boolean
  | natural

abbrev DataType.denote (type : DataType) : Type :=
  match type with
  | .text => String
  | .boolean => Bool
  | .natural => Nat

end Forms
