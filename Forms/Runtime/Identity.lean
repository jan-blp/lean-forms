module

public import Forms.Runtime.Feedback

@[expose] public section

namespace Forms.Runtime

inductive ControlKey where
  | edit (location : Feedback.Location)
  | select (location : Feedback.Location)
  | add (location : Feedback.Location)
  | remove (location : Feedback.Location)
  | selectRow (scope : List Nat) (row : Nat)
  | press (route : List Nat) (location : Feedback.Location)
  | tab (route : List Nat) (location : Feedback.Location)
  deriving DecidableEq

structure DomId where
  value : String
  deriving BEq, DecidableEq

end Forms.Runtime
