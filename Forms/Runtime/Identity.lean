module

public import Forms.Model.Diagnostic

@[expose] public section

namespace Forms.Runtime
open Forms.Model (ErasedLocation)

inductive ControlKey where
  | edit (location : ErasedLocation)
  | select (location : ErasedLocation)
  | press (route : List Nat) (location : ErasedLocation)
  | tab (route : List Nat) (location : ErasedLocation)
  /-- A control writing private state; `location` is where it sits, not what it edits. -/
  | state (route : List Nat) (location : ErasedLocation)
  deriving DecidableEq

def ControlKey.edits : ControlKey → Option ErasedLocation
  | .edit location => some location
  | .select location => some location
  | .press .. => none
  | .tab .. => none
  | .state .. => none

structure DomId where
  value : String
  deriving BEq, DecidableEq

end Forms.Runtime
