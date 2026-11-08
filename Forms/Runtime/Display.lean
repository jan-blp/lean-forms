module

public import Forms.Runtime.Identity
public import Forms.Runtime.Feedback

@[expose] public section

namespace Forms.Runtime.Display

inductive TargetStep where
  | name (value : String)
  | index (value : Nat)
  deriving BEq

abbrev Target := List TargetStep

inductive Editor where
  | text (value : String)
  | natural (value : Nat)
  | checkbox (value : Bool)
  deriving BEq

inductive ControlBody where
  | editor (location : Feedback.Location) (input : Editor)
  deriving BEq

structure Control where
  key : ControlKey
  id : String
  target : Target
  label : String
  disabled : Bool
  body : ControlBody
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
