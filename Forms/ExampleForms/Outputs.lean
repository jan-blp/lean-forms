module

public import Forms.Runtime.ModelView
public import Forms.Model.Sugar

@[expose] public section
namespace Forms.ExampleForms.Outputs
open Forms.Model Forms.Model.Sugar

def counter {Γ : Context} : Component Γ Nat Nat := named%
  state% count := (0 : Nat);
  state% hidden := (100 : Nat);
  .withOutput
    (.group "Counter" [
      .computed "Item" { inputs := inputs[path[]], run := toString },
      .computed "Owned count" { inputs := inputs[ref[count]], run := toString },
      .button "Increment" (.set ref[count] {
        inputs := inputs[ref[count]], run := fun n => n + 1 }),
      .computed "Private value" { inputs := inputs[ref[hidden]], run := toString },
      .button "Change private" (.set ref[hidden] {
        inputs := inputs[ref[hidden]], run := fun n => n + 1 })])
    { inputs := inputs[ref[count]], run := id }

def single : Component [] Nat Nat := named%
  .labeled "Owned counter output" <|
  observe% output := counter;
  state% remembered := (0 : Nat);
  .withOutput
    (.group "Observers" [
      .computed "Observer one" { inputs := inputs[ref[output]], run := toString },
      .computed "Observer two" {
        inputs := inputs[ref[output]], run := fun n => s!"Twice: {2 * n}" },
      .button "Remember output" (.set ref[remembered] {
        inputs := inputs[ref[output]], run := id }),
      .computed "Remembered" { inputs := inputs[ref[remembered]], run := toString }])
    { inputs := inputs[ref[output]], run := id }

def pair {Γ : Context} : Component Γ Nat Nat := named%
  observe% first := counter;
  observe% second := counter;
  let total : Computation _ Nat Nat := {
    inputs := inputs[ref[first], ref[second]], run := Nat.add }
  .withOutput (.computed "Pair sum" (toString <$> total)) total

def rows : Component [] (List (Item Nat)) (List Nat) :=
  .list .self "Pairs" (.numbered "Pair") "Add pair"
      (Item.mkWithoutUuid 0) (.zoom path[Item.Field.value] pair)

def nested : Component [] (List (Item Nat)) Nat := named%
  .labeled "Nested outputs" <|
  observe% totals := rows;
  let total : Computation _ (List (Item Nat)) Nat := {
    inputs := inputs[ref[totals]], run := List.sum }
  .withOutput (.group "Outer observers" [
    .computed "Pair totals" {
      inputs := inputs[ref[totals]]
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

def selectionCell
  {Γ : Context}
  (description : InputRef Γ String)
  : Component Γ (Item String) Bool := named%[description]
  state% selected := false;
  .withOutput
    (.group "" [
      .computed "Cell description" { inputs := inputs[ref[description]], run := id },
      .computed "Selection" { inputs := inputs[ref[selected]], run := toString },
      .button "Toggle selection" (.set ref[selected] {
        inputs := inputs[ref[selected]], run := Bool.not })])
    { inputs := inputs[ref[selected]], run := id }

def selectionColumns {Γ : Context} : Columns Γ (Item String) RowOutput := named%
  ⟨#v["Description", "Selected"],
    presentation%
      own% description := descriptionCell;
      own% selected := selectionCell ref[description];
      .layouts
        { inputs := inputs[ref[description], ref[selected]]
          run := fun description selected => { description, selected } }
        (.const #v[.place slot[description], .place slot[selected]])⟩

def selectionTable : Component [] (List (Item String)) (List RowOutput) :=
  .table .self "Items" (.numbered "Item") "Add item"
      (Item.mkWithoutUuid "New item") selectionColumns

/-- Two rows share a description, so selection must follow rows, not text. -/
def descriptions : List (Item String) :=
  IdGen.run (["Same description", "Same description", "Another item"].mapM Item.fresh)

end Forms.ExampleForms.Outputs
