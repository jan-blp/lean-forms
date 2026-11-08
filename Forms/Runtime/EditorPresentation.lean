module

public import Forms.Runtime.Display

@[expose] public section

namespace Forms.Runtime.EditorPresentation
open Display

inductive DraftInput where
  | text (value : String)
  | natural (value : Nat)

inductive ImmediateInput where
  | checkbox (checked : Bool)

inductive Presentation where
  | onApply (input : DraftInput)
  | onChange (input : ImmediateInput)

def ofEditor : Editor → Presentation
  | .text value => .onApply (.text value)
  | .natural value => .onApply (.natural value)
  | .checkbox value => .onChange (.checkbox value)

def DraftInput.value : DraftInput → String
  | .text value => value
  | .natural value => toString value

def draftValue (editor : Editor) : Option String :=
  match ofEditor editor with
  | .onApply input => some input.value
  | .onChange _ => none

end Forms.Runtime.EditorPresentation
