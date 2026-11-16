module

public import Forms.Runtime.Feedback

@[expose] public section

namespace Forms.Runtime
open Forms.Model (ErasedLocation)

inductive ControlKey where
  | edit (location : ErasedLocation)
  | select (location : ErasedLocation)
  | press (route : List Nat) (location : ErasedLocation)
  | tab (route : List Nat) (location : ErasedLocation)
  deriving DecidableEq

structure DomId where
  value : String
  deriving BEq, DecidableEq

end Forms.Runtime
