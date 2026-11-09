module

public import Forms.Runtime.Identity

@[expose] public section

namespace Forms.Runtime.Interaction

inductive Submission where
  | idle
  | requested
  | pending
  deriving Inhabited

inductive Notice where
  | info (message : String)
  | error (message : String)

structure State where
  submission : Submission
  notice : Notice
  resultVisible : Bool
  /-- Why the last event's `apply` was rejected. -/
  rejection : Option String

def State.initial : State where
  submission := .idle
  notice := .info ""
  resultVisible := false
  rejection := none

def State.pending (state : State) : Bool :=
  match state.submission with
  | .idle => false
  | _ => true

def State.send (state : State) : Bool :=
  match state.submission with
  | .requested => true
  | _ => false

def State.status (state : State) : String :=
  match state.notice with
  | .info message
  | .error message => message

def State.error (state : State) : Bool :=
  match state.notice with
  | .error _ => true
  | .info _ => false

def State.acknowledge (state : State) : State :=
  let submission := match state.submission with
    | .requested => .pending
    | other => other
  { state with submission }

def State.announce (state : State) (status : String) (error := false) : State :=
  { state with notice := if error then .error status else .info status }

end Forms.Runtime.Interaction
