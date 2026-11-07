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
  | select (selected : Nat) (options : List String)

inductive Presentation where
  | onApply (input : DraftInput)
  | onChange (input : ImmediateInput)

def ofEditor : Editor → Presentation
  | .text value => .onApply (.text value)
  | .natural value => .onApply (.natural value)
  | .date value => .onApply (.date value)
  | .checkbox value => .onChange (.checkbox value)
  | .select value options => .onChange (.select value options)

end Forms.Runtime.EditorPresentation
