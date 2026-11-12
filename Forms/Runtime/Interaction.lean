module

public import Forms.Runtime.Identity

@[expose] public section

namespace Forms.Runtime.Interaction

inductive Notice where
  | info (message : String)
  | error (message : String)

structure State where
  /-- A submission was sent and its outcome has not arrived. -/
  pending : Bool
  notice : Notice
  resultVisible : Bool
  /-- Why the last event's `apply` was rejected. -/
  rejection : Option String

def State.initial : State where
  pending := false
  notice := .info ""
  resultVisible := false
  rejection := none

def State.status (state : State) : String :=
  match state.notice with
  | .info message
  | .error message => message

def State.error (state : State) : Bool :=
  match state.notice with
  | .error _ => true
  | .info _ => false

def State.announce (state : State) (status : String) (error := false) : State :=
  { state with notice := if error then .error status else .info status }

end Forms.Runtime.Interaction
