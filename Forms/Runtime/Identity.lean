module

public import Forms.Runtime.Feedback

@[expose] public section

namespace Forms.Runtime

inductive ControlKey where
  | edit (location : Feedback.Location)
  | select (location : Feedback.Location)
  | press (route : List Nat) (location : Feedback.Location)
  | tab (route : List Nat) (location : Feedback.Location)
  deriving DecidableEq

structure DomId where
  value : String
  deriving BEq, DecidableEq

end Forms.Runtime
