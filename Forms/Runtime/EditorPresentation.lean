module

public import Forms.Runtime.Display

@[expose] public section

namespace Forms.Runtime.EditorPresentation
open Display

inductive DraftInput where
  | text (value : String)
  | natural (value : Nat)
  | date (value : Date)

inductive ImmediateInput where
  | checkbox (checked : Bool)
  | select (selection : Selection)

inductive Presentation where
  | onApply (input : DraftInput)
  | onChange (input : ImmediateInput)

def ofEditor : Editor → Presentation
  | .text value => .onApply (.text value)
  | .natural value => .onApply (.natural value)
  | .date value => .onApply (.date value)
  | .checkbox value => .onChange (.checkbox value)
  | .select selection => .onChange (.select selection)

def DraftInput.value : DraftInput → String
  | .text value => value
  | .natural value => toString value
  | .date value => Date.toString value

def draftValue (editor : Editor) : Option String :=
  match ofEditor editor with
  | .onApply input => some input.value
  | .onChange _ => none

end Forms.Runtime.EditorPresentation
