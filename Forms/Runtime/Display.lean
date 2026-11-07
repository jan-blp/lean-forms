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

structure Selection where
  options : List String
  selected : Fin options.length
  deriving BEq

def Selection.ofEnum (domain : Enum) (value : domain) : Selection :=
  { options := domain.options
    selected := ⟨(FinEnum.equiv value).val, by
      simp [Enum.options, FinEnum.toList]⟩ }

inductive Editor where
  | text (value : String)
  | natural (value : Nat)
  | date (value : Date)
  | checkbox (value : Bool)
  | select (selection : Selection)
  deriving BEq

inductive ControlKind where
  | button | editor | choice
  deriving BEq

inductive ControlBody where
  | button (keepDrafts : Bool)
  | editor (location : Feedback.Location) (input : Editor)
  | choice (location : Feedback.Location) (value : String) (options : List String)
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

def Control.kind (control : Control) : ControlKind :=
  match control.body with
  | .button _ => .button
  | .editor .. => .editor
  | .choice .. => .choice

inductive View where
  | hidden
  | control (control : Control)
  | stack (label : Option String) (children : List View)
  | actionWidget (label text : String) (location : Feedback.Location)
      (children : List Control) (messages : Option String)
  | list (label : String) (location : Feedback.Location)
      (items : List (View × Control)) (append : Control) (messages : Option String)
  | sum (selector : Control) (body : View)
  | computed (label text : String)
  | text (value : String)
  | table (columns : List String) (rows : List (List String))
  deriving BEq

def View.isHidden : View → Bool
  | .hidden => true
  | _ => false

def View.title (view : View) : String :=
  let label := match view with
    | .control c => c.label
    | .stack label _ => label.getD ""
    | .actionWidget label .. | .list label .. | .computed label .. => label
    | _ => ""
  if label.isEmpty then "Form" else label

end Forms.Runtime.Display
