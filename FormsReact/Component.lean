module

public import Lean.Data.Json

@[expose] public section
namespace FormsReact
open Lean

/-- What a component asks the form to do. -/
inductive Action where
  | apply (name : String)
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

/-- A text input whose draft React owns; `onCommit` receives the draft text. -/
structure TextField where
  name : String
  label : String
  value : String
  disabled : Bool
  error : Option String
  onCommit : Action
  deriving ToJson, FromJson, BEq, Repr

/-- A non-negative whole number input; `onCommit` receives the draft text, which Lean decodes. -/
structure NaturalField where
  name : String
  label : String
  /-- Decimal digits, so values beyond 2^53 survive JavaScript. -/
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

/-- A read-only computed value. -/
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

mutual
/-- Children grouped under an optional legend. -/
structure Group where
  label : Option String
  children : List Component

structure Page where
  title : String
  busy : Bool
  body : List Component
  toolbar : List Component
  notice : Notice
  /-- The submitted value, once there is one to show. -/
  result : Option String

inductive Component where
  | textField : TextField → Component
  | naturalField : NaturalField → Component
  | checkbox : Checkbox → Component
  | output : Output → Component
  | button : Button → Component
  | group : Group → Component
  | page : Page → Component
end

deriving instance ToJson, FromJson, BEq, Repr for Group, Page, Component

mutual
/-- Names of the enabled fields that commit typed text, whose drafts React keeps. -/
def Component.draftFields : Component → List String
  | .textField field => if field.disabled then [] else [field.name]
  | .naturalField field => if field.disabled then [] else [field.name]
  | .checkbox _ => []
  | .output _ => []
  | .button _ => []
  | .group { children, .. } => draftFieldsOf children
  | .page { body, toolbar, .. } => draftFieldsOf body ++ draftFieldsOf toolbar

def draftFieldsOf : List Component → List String
  | [] => []
  | component :: rest => component.draftFields ++ draftFieldsOf rest
end

end FormsReact
