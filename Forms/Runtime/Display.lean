module

public import Forms.Runtime.Identity
public import Forms.Model.Diagnostic
public import Forms.Model.Format

@[expose] public section

namespace Forms.Runtime.Display
open Forms.Model (ErasedLocation)

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
  | text (kind : Model.TextKind) (value : String)
  | checkbox (value : Bool)
  /-- `selected` is the active option's `value`, or empty when no option matches. -/
  | choice (selected : String) (options : List ChoiceOption)
  /-- Its argument is the picked options' values. -/
  | choices (selected : List String) (options : List ChoiceOption)
  /-- A button; its argument is ignored. -/
  | action
  /-- Tab labels with `active` selected; its argument is the chosen tab's index. -/
  | tabs (active : Nat) (labels : List String)
  deriving BEq

structure Control where
  key : ControlKey
  target : Target
  label : String
  disabled : Bool
  location : ErasedLocation
  input : Editor
  messages : List String
  deriving BEq

mutual
inductive View where
  | hidden
  | control (control : Control)
  | stack (label : Option String) (children : List View)
  | computed (label text : String)
  /-- `messages` are about the list as a whole. -/
  | list (label : String) (children : List View) (messages : List String)
  | table (label : String) (headers : List String) (rows : List TableRow)
      (footer : View) (messages : List String)

structure TableRow where
  label : String
  cells : List View
  selected : Option Bool
end

deriving instance BEq for View, TableRow

def View.ofList : List View → View
  | [] => .hidden
  | [view] => view
  | views => .stack none views

mutual
def View.controls : View → List Control
  | .control c => [c]
  | .stack _ children => View.controlsAll children
  | .list (children := children) .. => View.controlsAll children
  | .table (rows := rows) (footer := footer) .. => View.controlsRows rows ++ footer.controls
  | .hidden => []
  | .computed .. => []

def View.controlsAll : List View → List Control
  | [] => []
  | view :: rest => view.controls ++ View.controlsAll rest

def View.controlsRows : List TableRow → List Control
  | [] => []
  | { cells, .. } :: rest => View.controlsAll cells ++ View.controlsRows rest
end

def duplicateNote : String := "Duplicate control: this value is edited elsewhere in the form."

structure DedupeResult (α : Type) where
  deduped : α
  seen : List ControlKey

mutual
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

def Control.editable (control : Control) : Bool :=
  !control.disabled && match control.input with
    | .action => false
    | .tabs .. => false
    | _ => true

def View.resolve
  (view : View)
  (locations : List ErasedLocation)
  : Option ControlKey :=
  let controls := view.controls.filter Control.editable
  let exact := controls.find? fun control => locations.contains control.location
  let descendant := controls.find? fun control =>
    locations.any (·.isPrefixOf control.location)
  (exact.orElse fun _ => descendant).map (·.key)

/-- Resolves each target list on its own, then picks the earliest result in rendered order. -/
def View.resolveFirst
  (view : View)
  (targets : List (List ErasedLocation))
  : Option ControlKey :=
  let keys := targets.filterMap view.resolve
  (view.controls.find? fun control => keys.contains control.key).map (·.key)

end Forms.Runtime.Display
