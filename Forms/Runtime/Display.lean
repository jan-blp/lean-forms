module

public import Forms.Runtime.Identity
public import Forms.Runtime.Feedback

@[expose] public section

namespace Forms.Runtime.Display

/-- A control's layout position, represented by zero-based child indices through nested groups.
Used to generate its browser key. -/
structure Target where
  indices : List Nat := []
  deriving BEq

def Target.child (target : Target) (index : Nat) : Target :=
  ⟨target.indices ++ [index]⟩

inductive Editor where
  | text (value : String)
  | natural (value : Nat)
  | checkbox (value : Bool)
  deriving BEq

structure Control where
  key : ControlKey
  target : Target
  label : String
  disabled : Bool
  location : Feedback.Location
  input : Editor
  messages : Option String := none
  deriving BEq

inductive View where
  | hidden
  | control (control : Control)
  | stack (label : Option String) (children : List View)
  | computed (label text : String)
  deriving BEq

def View.title (view : View) : String :=
  let label := match view with
    | .control c => c.label
    | .stack label _ => label.getD ""
    | .computed label .. => label
    | _ => ""
  if label.isEmpty then "Form" else label

end Forms.Runtime.Display
