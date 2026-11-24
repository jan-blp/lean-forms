module

public import Forms.Runtime.Identity
public import Forms.Model.Diagnostic
public import Forms.Model.Evidence
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
  deriving DecidableEq

inductive Evidence where
  | unsupported
  | missing
  /-- `stale` when the cells' text no longer reads as the current value. -/
  | linked (evidence : Model.Evidence) (stale : Bool)
  deriving DecidableEq

/-- A lookup's matches for its search text. -/
inductive SearchResults where
  | loading
  | failed (message : String)
  /-- `more` when the server left some matches out. -/
  | found (options : List ChoiceOption) (more : Bool)
  deriving DecidableEq

structure Search where
  text : String
  results : SearchResults
  deriving DecidableEq

/-- How a field shows its value. -/
inductive Value where
  | text (kind : Model.TextKind) (value : String)
  | checkbox (value : Bool)
  /-- Its argument is the picked options' values. -/
  | choices (selected : List String) (options : List ChoiceOption)
  deriving DecidableEq

inductive Editor where
  | field (value : Value) (evidence : Evidence)
  /-- `selected` is the active option's `value`, or empty when no option matches. -/
  | choice (selected : String) (options : List ChoiceOption)
  /-- Picks a server record; `search` is present while searching. -/
  | lookup (picked : Option ChoiceOption) (search : Option Search)
  /-- A button; its argument is ignored. -/
  | action
  /-- Tab labels with `active` selected; its argument is the chosen tab's index. -/
  | tabs (active : Nat) (labels : List String)
  deriving DecidableEq

structure Control where
  key : ControlKey
  target : Target
  label : String
  disabled : Bool
  location : ErasedLocation
  input : Editor
  messages : List Model.Message
  deriving BEq

def Control.errors (control : Control) : List String :=
  Model.Message.errors control.messages

mutual
inductive View where
  | hidden
  | control (control : Control)
  | stack (label : Option String) (children : List View)
  | computed (label text : String)
  | marker (reports : List Model.ReportMessage)
  /-- `messages` are about the list as a whole. -/
  | list (label : String) (children : List View) (messages : List Model.Message)
  | table (label : String) (headers : List String) (rows : List TableRow)
      (footer : View) (messages : List Model.Message)
  /-- A list row, kept apart from its siblings by its item id. -/
  | keyed (key : Model.Uuid) (body : View)

structure TableRow where
  key : Model.Uuid
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
  | .keyed _ body => body.controls
  | .hidden => []
  | .computed .. => []
  | .marker _ => []

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
  | .keyed key body =>
    let result := body.dedupeFrom seen
    { deduped := .keyed key result.deduped, seen := result.seen }
  | .hidden => { deduped := .hidden, seen }
  | .computed label text => { deduped := .computed label text, seen }
  | .marker reports => { deduped := .marker reports, seen }

def View.dedupeAll (seen : List ControlKey) : List View → DedupeResult (List View)
  | [] => { deduped := [], seen }
  | view :: rest =>
    let head := view.dedupeFrom seen
    let tail := View.dedupeAll head.seen rest
    { deduped := head.deduped :: tail.deduped, seen := tail.seen }

def View.dedupeRows (seen : List ControlKey) : List TableRow → DedupeResult (List TableRow)
  | [] => { deduped := [], seen }
  | ⟨key, label, cells, selected⟩ :: rest =>
    let head := View.dedupeAll seen cells
    let tail := View.dedupeRows head.seen rest
    { deduped := ⟨key, label, head.deduped, selected⟩ :: tail.deduped, seen := tail.seen }
end

/-- Replaces each control whose key appeared earlier with a note. -/
def View.dedupe (view : View) : View :=
  (view.dedupeFrom []).deduped

def View.title (view : View) : String :=
  let rec labelOf : View → String
    | .control c => c.label
    | .stack label _ => label.getD ""
    | .list label .. => label
    | .table label .. => label
    | .computed label .. => label
    | .marker _ => ""
    | .keyed _ body => labelOf body
    | .hidden => ""
  let title := labelOf view
  if title.isEmpty then "Form" else title

def Control.editable (control : Control) : Bool :=
  !control.disabled && match control.input with
    | .field (.text ..) _ => true
    | .field (.checkbox _) _ => true
    | .field (.choices ..) _ => true
    | .choice .. => true
    | .lookup .. => true
    | .action => false
    | .tabs .. => false

/-- Whether the control keeps uncommitted text, whose errors become draft diagnostics. -/
def Control.acceptsDrafts (control : Control) : Bool :=
  !control.disabled && match control.input with
    | .field (.text ..) _ => true
    | .field (.checkbox _) _ => false
    | .field (.choices ..) _ => false
    | .choice .. => false
    | .lookup .. => false
    | .action => false
    | .tabs .. => false

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
