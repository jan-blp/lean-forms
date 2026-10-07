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

scoped notation "⟦" t "⟧" => DataType.denote t

end Forms
