module

public import Forms.Runtime.Identity

public section

namespace Forms.Runtime.Interaction

inductive Submission where
  | idle | requested | pending
  deriving Inhabited

inductive Notice where
  | info (message : String)
  | error (message : String)

structure State where
  drafts : List (ControlKey × String) := []
  submission : Submission := .idle
  notice : Notice := .info ""
  resultVisible : Bool := false
  focus : Option ControlKey := none
  deriving Inhabited

def State.pending (state : State) : Bool :=
  match state.submission with | .idle => false | _ => true

def State.send (state : State) : Bool :=
  match state.submission with | .requested => true | _ => false

def State.status (state : State) : String :=
  match state.notice with | .info message | .error message => message

def State.error (state : State) : Bool :=
  match state.notice with | .error _ => true | .info _ => false

def State.acknowledge (state : State) : State :=
  { state with submission := match state.submission with | .requested => .pending | other => other, focus := none }

def State.announce (state : State) (status : String) (error := false) : State :=
  { state with notice := if error then .error status else .info status }

end Forms.Runtime.Interaction
