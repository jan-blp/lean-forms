module

public import Lean.Data.Json

@[expose] public section
namespace FormsReact
open Lean

inductive Action where
  | apply (name : String)
  /-- Presses button `name`; pending drafts are applied first. -/
  | press (name : String)
  | submit
  | reset
  deriving ToJson, FromJson, BEq, Repr

inductive Notice where
  | info (message : String)
  | error (message : String)
  deriving ToJson, FromJson, BEq, Repr

inductive ButtonVariant where
  | primary
  | secondary
  deriving ToJson, FromJson, BEq, Repr

/-- Which input edits the text; Lean parses what is committed. -/
inductive TextKind where
  | plain
  | natural
  | integer
  | decimal
  | date
  | uuid
  deriving ToJson, FromJson, BEq, Repr

inductive Commit where
  | onLeave
  | whileTyping
  deriving ToJson, FromJson, BEq, Repr

/-- The colour of a status marker. -/
inductive Tone where
  | attention
  | outdated
  | resolved
  | info
  deriving ToJson, FromJson, BEq, DecidableEq, Repr

/-- Checks grouped for a status marker. -/
structure Checks where
  tone : Tone
  unresolved : List String
  outdated : List String
  resolved : List String
  approved : List String
  info : List String
  outdatedInfo : List String
  deriving ToJson, FromJson, BEq, DecidableEq, Repr

inductive Evidence where
  | unsupported
  | missing
  /-- `stale` when the value no longer matches the cells' text. -/
  | linked (page : Nat) (cellIds : List Nat) (stale : Bool)
  deriving ToJson, FromJson, BEq, Repr

/-- Whether the field takes a pick from the document. -/
def Evidence.picks : Evidence → Bool
  | .unsupported => false
  | .missing => true
  | .linked .. => true

/-- A text input whose draft React owns; `onCommit` receives the draft text, or
`{ "pick": Forms.Model.Evidence }` when the field takes evidence. Values travel as text, so numbers
beyond 2^53 survive JavaScript. -/
structure TextField where
  name : String
  label : String
  kind : TextKind
  value : String
  commit : Commit
  disabled : Bool
  errors : List String
  evidence : Evidence
  onCommit : Action
  deriving ToJson, FromJson, BEq, Repr

/-- `onChange` receives the new checked state, or `{ "pick": Forms.Model.Evidence }`. -/
structure Checkbox where
  name : String
  label : String
  checked : Bool
  disabled : Bool
  errors : List String
  evidence : Evidence
  onChange : Action
  deriving ToJson, FromJson, BEq, Repr

structure ChoiceOption where
  value : String
  label : String
  deriving ToJson, FromJson, BEq, Repr

structure SelectableOption where
  value : String
  label : String
  disabledReason : Option String
  deriving ToJson, FromJson, BEq, Repr

/-- Picks one of `options`; `onChange` receives the chosen option's `value`. -/
structure Choice where
  name : String
  label : String
  value : String
  options : List SelectableOption
  disabled : Bool
  errors : List String
  onChange : Action
  deriving ToJson, FromJson, BEq, Repr

/-- `onChange` receives the picked options' `value`s, or `{ "pick": Forms.Model.Evidence }`. -/
structure Choices where
  name : String
  label : String
  values : List String
  options : List ChoiceOption
  disabled : Bool
  errors : List String
  evidence : Evidence
  onChange : Action
  deriving ToJson, FromJson, BEq, Repr

inductive SearchResults where
  | loading
  | failed (message : String)
  | found (options : List SelectableOption) (more : Bool)
  deriving ToJson, FromJson, BEq, Repr

structure Search where
  text : String
  results : SearchResults
  deriving ToJson, FromJson, BEq, Repr

inductive LookupInput where
  | search (text : String)
  | close
  | choose (key : String)
  | clear
  deriving ToJson, FromJson, BEq, Repr

/-- `onChange` receives `{ "lookup": command }` with a `LookupInput` command. -/
structure Lookup where
  name : String
  label : String
  picked : Option ChoiceOption
  search : Option Search
  disabled : Bool
  errors : List String
  onChange : Action
  deriving ToJson, FromJson, BEq, Repr

structure Output where
  label : String
  value : String
  deriving ToJson, FromJson, BEq, Repr

structure Button where
  label : String
  variant : ButtonVariant
  disabled : Bool
  onClick : Action
  deriving ToJson, FromJson, BEq, Repr

/-- Shows which tab is `active`; `onChange` receives the chosen tab's index as decimal text. -/
structure TabBar where
  name : String
  label : String
  active : Nat
  labels : List String
  disabled : Bool
  onChange : Action
  deriving ToJson, FromJson, BEq, Repr

mutual
/-- Children grouped under an optional legend; `errors` are about the group as a whole. -/
structure Group where
  label : Option String
  children : List Component
  errors : List String
  /-- The item id of a list row; React keeps the row's state when siblings move. -/
  key : Option String

structure TableRow where
  key : String
  label : String
  cells : List Component
  selected : Option Bool

structure Table where
  label : String
  headers : List String
  rows : List TableRow
  footer : Component
  errors : List String

structure Page where
  title : String
  busy : Bool
  body : List Component
  toolbar : List Component
  notice : Notice
  result : Option String

inductive Component where
  | textField : TextField → Component
  | checkbox : Checkbox → Component
  | choice : Choice → Component
  | choices : Choices → Component
  | lookup : Lookup → Component
  | output : Output → Component
  | button : Button → Component
  | tabBar : TabBar → Component
  | group : Group → Component
  | table : Table → Component
  | page : Page → Component
  | statusMarker : Checks → Component
end

deriving instance ToJson, FromJson, BEq, Repr for Group, TableRow, Table, Page, Component

mutual
/-- Names of the enabled fields that commit typed text, whose drafts React keeps. -/
def Component.draftFields : Component → List String
  | .textField field => if field.disabled then [] else [field.name]
  | .checkbox _ => []
  | .choice _ => []
  | .choices _ => []
  | .lookup _ => []
  | .output _ => []
  | .button _ => []
  | .tabBar _ => []
  | .group { children, .. } => draftFieldsOf children
  | .table { rows, footer, .. } => draftFieldsOfRows rows ++ footer.draftFields
  | .page { body, toolbar, .. } => draftFieldsOf body ++ draftFieldsOf toolbar
  | .statusMarker _ => []

def draftFieldsOf : List Component → List String
  | [] => []
  | component :: rest => component.draftFields ++ draftFieldsOf rest

def draftFieldsOfRows : List TableRow → List String
  | [] => []
  | ⟨_, _, cells, _⟩ :: rest => draftFieldsOf cells ++ draftFieldsOfRows rest
end

def pickField (name : String) (disabled : Bool) (evidence : Evidence) : List String :=
  if !disabled && evidence.picks then [name] else []

mutual
/-- Names of the enabled fields that take a pick from the document. -/
def Component.pickFields : Component → List String
  | .textField { name, disabled, evidence, .. } => pickField name disabled evidence
  | .checkbox { name, disabled, evidence, .. } => pickField name disabled evidence
  | .choices { name, disabled, evidence, .. } => pickField name disabled evidence
  | .choice _ => []
  | .lookup _ => []
  | .output _ => []
  | .button _ => []
  | .tabBar _ => []
  | .group { children, .. } => pickFieldsOf children
  | .table { rows, footer, .. } => pickFieldsOfRows rows ++ footer.pickFields
  | .page { body, toolbar, .. } => pickFieldsOf body ++ pickFieldsOf toolbar
  | .statusMarker _ => []

def pickFieldsOf : List Component → List String
  | [] => []
  | component :: rest => component.pickFields ++ pickFieldsOf rest

def pickFieldsOfRows : List TableRow → List String
  | [] => []
  | { cells, .. } :: rest => pickFieldsOf cells ++ pickFieldsOfRows rest
end

end FormsReact
