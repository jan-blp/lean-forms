module

public import Forms.Runtime.ModelView

@[expose] public section
namespace Forms.ExampleForms.Outputs
open Forms.Model

def counter {Γ : Context} : Component Γ Nat Nat :=
  .bind (0 : Nat) <|
    .bind (100 : Nat) <|
      let count : Var (⟨.writable, Nat⟩ :: ⟨.writable, Nat⟩ :: Γ) Nat := .there .here
      let hidden : Var (⟨.writable, Nat⟩ :: ⟨.writable, Nat⟩ :: Γ) Nat := .here
      .withOutput
        (.group "Counter" [
          .computed "Item" { inputs := inputs[path[]], run := toString },
          .computed "Owned count" { inputs := inputs[.ui count], run := toString },
          .button "Increment" (.set count { inputs := inputs[.ui count], run := fun n => n + 1 }),
          .computed "Private value" { inputs := inputs[.ui hidden], run := toString },
          .button "Change private" (.set hidden { inputs := inputs[.ui hidden], run := fun n => n + 1 })])
        { inputs := inputs[.ui count], run := id }

def single : Component [] Nat Nat :=
  .labeled "Owned counter output" <|
  .observe counter <|
    .bind (0 : Nat) <|
      let output : InputRef [⟨.writable, Nat⟩, ⟨.readOnly, Nat⟩] Nat := .there .here
      let remembered : Var [⟨.writable, Nat⟩, ⟨.readOnly, Nat⟩] Nat := .here
      .withOutput
        (.group "Observers" [
          .computed "Observer one" { inputs := inputs[.ui output], run := toString },
          .computed "Observer two" { inputs := inputs[.ui output], run := fun n => s!"Twice: {2 * n}" },
          .button "Remember output" (.set remembered { inputs := inputs[.ui output], run := id }),
          .computed "Remembered" { inputs := inputs[.ui remembered], run := toString }])
        { inputs := inputs[.ui output], run := id }

def pair {Γ : Context} : Component Γ Nat Nat :=
  .observe counter <|
    .observe counter <|
      let first : InputRef (⟨.readOnly, Nat⟩ :: ⟨.readOnly, Nat⟩ :: Γ) Nat := .there .here
      let second : InputRef (⟨.readOnly, Nat⟩ :: ⟨.readOnly, Nat⟩ :: Γ) Nat := .here
      let total : Computation (⟨.readOnly, Nat⟩ :: ⟨.readOnly, Nat⟩ :: Γ) Nat Nat := {
        inputs := inputs[.ui first, .ui second], run := Nat.add }
      .withOutput (.computed "Pair sum" (toString <$> total)) total

def rows : Component [] (List Nat) (List Nat) :=
  .list .self "Pairs" "Pair" 0 pair

def nested : Component [] (List Nat) Nat :=
  .labeled "Nested outputs" <|
  .observe rows <|
    let total : Computation [⟨.readOnly, List Nat⟩] (List Nat) Nat := {
      inputs := inputs[.ui (Ref.here : InputRef _ (List Nat))], run := List.sum }
    .withOutput (.group "Outer observers" [
      .computed "Pair totals" {
        inputs := inputs[.ui (Ref.here : InputRef _ (List Nat))]
        run := fun values => String.intercalate ", " (values.map toString) },
      .computed "Overall sum" (toString <$> total)]) total

def repeated : Component [] (List Nat) :=
  .group "Outputs of owned counters" [
    .observe (Component.list .self "Counters" "Counter" 0 counter) <|
      let counts : InputRef [⟨.readOnly, List Nat⟩] (List Nat) := .here
      .group "Observers outside the list" [
        .computed "Counts" {
          inputs := inputs[.ui counts]
          run := fun values => String.intercalate ", " (values.map toString) },
        .computed "Sum" { inputs := inputs[.ui counts], run := fun values => toString values.sum }]]

def initial : List Nat := [10, 20]

structure RowOutput where
  description : String
  selected : Bool
  deriving BEq, Repr

def descriptionCell {Γ : Context} : Component Γ String String :=
  .withOutput (.field .self "Description" .text) { inputs := inputs[path[]], run := id }

def selectionCell {Γ : Context} : Component (⟨.readOnly, String⟩ :: Γ) String Bool :=
  .bind false <|
    let selected : Var (⟨.writable, Bool⟩ :: ⟨.readOnly, String⟩ :: Γ) Bool := .here
    let description : InputRef (⟨.writable, Bool⟩ :: ⟨.readOnly, String⟩ :: Γ) String := .there .here
    .withOutput
      (.group "" [
        .computed "Cell description" { inputs := inputs[.ui description], run := id },
        .computed "Selection" { inputs := inputs[.ui selected], run := toString },
        .button "Toggle selection" (.set selected { inputs := inputs[.ui selected], run := Bool.not })])
      { inputs := inputs[.ui selected], run := id }

def selectionColumns {Γ : Context} : Columns Γ String RowOutput :=
  Columns.observe "Description" descriptionCell <|
    Columns.observe "Selected" selectionCell <|
      let description : InputRef (⟨.readOnly, Bool⟩ :: ⟨.readOnly, String⟩ :: Γ) String := .there .here
      let selected : InputRef (⟨.readOnly, Bool⟩ :: ⟨.readOnly, String⟩ :: Γ) Bool := .here
      .output {
        inputs := inputs[.ui description, .ui selected]
        run := fun description selected => { description, selected } }

def selectionTable : Component [] (List String) (List RowOutput) :=
  .table .self "Items" "Item" "New item" selectionColumns

def selectedDescriptions : Component [] (List String) String :=
  .labeled "Row-local selection" <|
  .observe selectionTable <|
    let summary : Computation [⟨.readOnly, List RowOutput⟩] (List String) String := {
      inputs := inputs[.ui (Ref.here : InputRef _ (List RowOutput))]
      run := fun rows => String.intercalate ", " ((rows.filter (·.selected)).map (·.description)) }
    .withOutput (.computed "Selected descriptions" summary) summary

end Forms.ExampleForms.Outputs
