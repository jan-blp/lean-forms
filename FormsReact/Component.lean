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

/-- A text input whose draft React owns; `onCommit` receives the draft text.
Values travel as text, so numbers beyond 2^53 survive JavaScript. -/
structure TextField where
  name : String
  label : String
  kind : TextKind
  value : String
  disabled : Bool
  error : Option String
  onCommit : Action
  deriving ToJson, FromJson, BEq, Repr

/-- `onChange` receives the new checked state. -/
structure Checkbox where
  name : String
  label : String
  checked : Bool
  disabled : Bool
  error : Option String
  onChange : Action
  deriving ToJson, FromJson, BEq, Repr

structure ChoiceOption where
  value : String
  label : String
  deriving ToJson, FromJson, BEq, Repr

/-- Picks one of `options`; `onChange` receives the chosen option's `value`. -/
structure Choice where
  name : String
  label : String
  value : String
  options : List ChoiceOption
  disabled : Bool
  error : Option String
  onChange : Action
  deriving ToJson, FromJson, BEq, Repr

/-- `onChange` receives the picked options' `value`s. -/
structure Choices where
  name : String
  label : String
  values : List String
  options : List ChoiceOption
  disabled : Bool
  error : Option String
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
/-- Children grouped under an optional legend; `error` is about the group as a whole. -/
structure Group where
  label : Option String
  children : List Component
  error : Option String

structure TableRow where
  label : String
  cells : List Component
  selected : Option Bool

structure Table where
  label : String
  headers : List String
  rows : List TableRow
  footer : Component
  error : Option String

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
  | output : Output → Component
  | button : Button → Component
  | tabBar : TabBar → Component
  | group : Group → Component
  | table : Table → Component
  | page : Page → Component
end

deriving instance ToJson, FromJson, BEq, Repr for Group, TableRow, Table, Page, Component

mutual
/-- Names of the enabled fields that commit typed text, whose drafts React keeps. -/
def Component.draftFields : Component → List String
  | .textField field => if field.disabled then [] else [field.name]
  | .checkbox _ => []
  | .choice _ => []
  | .choices _ => []
  | .output _ => []
  | .button _ => []
  | .tabBar _ => []
  | .group { children, .. } => draftFieldsOf children
  | .table { rows, footer, .. } => draftFieldsOfRows rows ++ footer.draftFields
  | .page { body, toolbar, .. } => draftFieldsOf body ++ draftFieldsOf toolbar

def draftFieldsOf : List Component → List String
  | [] => []
  | component :: rest => component.draftFields ++ draftFieldsOf rest

def draftFieldsOfRows : List TableRow → List String
  | [] => []
  | ⟨_, cells, _⟩ :: rest => draftFieldsOf cells ++ draftFieldsOfRows rest
end

end FormsReact
