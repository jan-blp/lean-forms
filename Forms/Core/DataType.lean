import Forms.Core.Date
namespace Forms

inductive DataType where
  | text
  | boolean
  | natural
  | date

abbrev DataType.denote (type : DataType) : Type :=
  match type with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .date => Date

end Forms
