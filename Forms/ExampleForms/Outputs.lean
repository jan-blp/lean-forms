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

def rows : Component [] (List (Item Nat)) (List Nat) :=
  .list .self "Pairs" (.numbered "Pair") "Add pair"
      (Item.mkWithoutUuid 0) (.zoom path[Item.Field.value] pair)

def nested : Component [] (List (Item Nat)) Nat :=
  .labeled "Nested outputs" <|
  .observe rows <|
    let total : Computation [⟨.readOnly, List Nat⟩] (List (Item Nat)) Nat := {
      inputs := inputs[.ui (Ref.here : InputRef _ (List Nat))], run := List.sum }
    .withOutput (.group "Outer observers" [
      .computed "Pair totals" {
        inputs := inputs[.ui (Ref.here : InputRef _ (List Nat))]
        run := fun values => String.intercalate ", " (values.map toString) },
      .computed "Overall sum" (toString <$> total)]) total

def initial : List (Item Nat) := IdGen.run ([10, 20].mapM Item.fresh)

structure RowOutput where
  description : String
  selected : Bool
  deriving BEq, Repr

def descriptionCell {Γ : Context} : Component Γ (Item String) String :=
  .zoom path[Item.Field.value] <|
    .withOutput (.field .self "Description" .text) { inputs := inputs[path[]], run := id }

def selectionCell {Γ : Context} : Component (⟨.readOnly, String⟩ :: Γ) (Item String) Bool :=
  .bind false <|
    let selected : Var (⟨.writable, Bool⟩ :: ⟨.readOnly, String⟩ :: Γ) Bool := .here
    let description : InputRef (⟨.writable, Bool⟩ :: ⟨.readOnly, String⟩ :: Γ) String := .there .here
    .withOutput
      (.group "" [
        .computed "Cell description" { inputs := inputs[.ui description], run := id },
        .computed "Selection" { inputs := inputs[.ui selected], run := toString },
        .button "Toggle selection" (.set selected { inputs := inputs[.ui selected], run := Bool.not })])
      { inputs := inputs[.ui selected], run := id }

def selectionColumns {Γ : Context} : Columns Γ (Item String) RowOutput :=
  ⟨#v["Description", "Selected"],
    .own descriptionCell <|
      .own selectionCell <|
        let description : InputRef (⟨.readOnly, Bool⟩ :: ⟨.readOnly, String⟩ :: Γ) String :=
          .there .here
        let selected : InputRef (⟨.readOnly, Bool⟩ :: ⟨.readOnly, String⟩ :: Γ) Bool := .here
        .layouts
          { inputs := inputs[.ui description, .ui selected]
            run := fun description selected => { description, selected } }
          (.const #v[.place (.there .here), .place .here])⟩

def selectionTable : Component [] (List (Item String)) (List RowOutput) :=
  .table .self "Items" (.numbered "Item") "Add item"
      (Item.mkWithoutUuid "New item") selectionColumns

/-- Two rows share a description, so selection must follow rows, not text. -/
def descriptions : List (Item String) :=
  IdGen.run (["Same description", "Same description", "Another item"].mapM Item.fresh)

end Forms.ExampleForms.Outputs
