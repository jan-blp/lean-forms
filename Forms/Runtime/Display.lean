module

public import Forms.Runtime.Identity
public import Forms.Runtime.Feedback

@[expose] public section

namespace Forms.Runtime.Display

/-- A control's position in the component tree, as zero-based child indices; actions are decoded
along it. -/
structure Target where
  indices : List Nat := []
  deriving BEq

def Target.child (target : Target) (index : Nat) : Target :=
  ⟨target.indices ++ [index]⟩

structure ChoiceOption where
  value : String
  label : String
  deriving BEq

inductive Editor where
  | text (value : String)
  | natural (value : Nat)
  | checkbox (value : Bool)
  /-- `selected` is the active option's `value`, or empty when no option matches. -/
  | choice (selected : String) (options : List ChoiceOption)
  /-- A button; its argument is ignored. -/
  | action
  deriving BEq

/-- An interactive leaf of the view: an editor or button bound to one form value. -/
structure Control where
  key : ControlKey
  target : Target
  label : String
  disabled : Bool
  location : Feedback.Location
  input : Editor
  messages : Option String := none
  deriving BEq

mutual
inductive View where
  | hidden
  | control (control : Control)
  | stack (label : Option String) (children : List View)
  | computed (label text : String)
  /-- Items, then the add button; `messages` are about the list as a whole. -/
  | list (label : String) (children : List View) (messages : Option String)
  | table (label : String) (headers : List String) (rows : List TableRow)
      (footer : View) (messages : Option String)

structure TableRow where
  label : String
  cells : List View
  selected : Option Bool := none
end

deriving instance BEq for View, TableRow

mutual
/-- The controls of `view`, in display order. -/
def View.controls : View → List Control
  | .control c => [c]
  | .stack _ children => View.controlsAll children
  | .list _ children _ => View.controlsAll children
  | .table _ _ rows footer _ => View.controlsRows rows ++ footer.controls
  | .hidden => []
  | .computed .. => []

def View.controlsAll : List View → List Control
  | [] => []
  | view :: rest => view.controls ++ View.controlsAll rest

def View.controlsRows : List TableRow → List Control
  | [] => []
  | ⟨_, cells, _⟩ :: rest => View.controlsAll cells ++ View.controlsRows rest
end

def duplicateNote : String := "Duplicate control: this value is edited elsewhere in the form."

/-- A deduplicated value and the control keys seen so far, including the initial keys. -/
structure DedupeResult (α : Type) where
  deduped : α
  seen : List ControlKey

mutual
/-- Replaces each control whose key is in `seen` with a note; returns the keys seen after. -/
def View.dedupeFrom (seen : List ControlKey) : View → DedupeResult View
  | .control c =>
    if c.key ∈ seen then
      { deduped := .computed c.label duplicateNote, seen }
    else
      { deduped := .control c, seen := c.key :: seen }
  | .stack label children =>
    let result := View.dedupeAll seen children
    { deduped := .stack label result.deduped, seen := result.seen }
  | .list label children messages =>
    let result := View.dedupeAll seen children
    { deduped := .list label result.deduped messages, seen := result.seen }
  | .table label headers rows footer messages =>
    let rows := View.dedupeRows seen rows
    let footer := footer.dedupeFrom rows.seen
    { deduped := .table label headers rows.deduped footer.deduped messages, seen := footer.seen }
  | .hidden => { deduped := .hidden, seen }
  | .computed label text => { deduped := .computed label text, seen }

def View.dedupeAll (seen : List ControlKey) : List View → DedupeResult (List View)
  | [] => { deduped := [], seen }
  | view :: rest =>
    let head := view.dedupeFrom seen
    let tail := View.dedupeAll head.seen rest
    { deduped := head.deduped :: tail.deduped, seen := tail.seen }

def View.dedupeRows (seen : List ControlKey) : List TableRow → DedupeResult (List TableRow)
  | [] => { deduped := [], seen }
  | ⟨label, cells, selected⟩ :: rest =>
    let head := View.dedupeAll seen cells
    let tail := View.dedupeRows head.seen rest
    { deduped := ⟨label, head.deduped, selected⟩ :: tail.deduped, seen := tail.seen }
end

/-- Replaces each control whose key appeared earlier with a note. -/
def View.dedupe (view : View) : View :=
  (view.dedupeFrom []).deduped

def View.title (view : View) : String :=
  let label := match view with
    | .control c => c.label
    | .stack label _ => label.getD ""
    | .list label .. => label
    | .table label .. => label
    | .computed label .. => label
    | _ => ""
  if label.isEmpty then "Form" else label

end Forms.Runtime.Display
