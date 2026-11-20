module

public import Forms.ExampleForms.Outputs

@[expose] public section
namespace Forms.ExampleForms.Presentation
open Forms.Model Forms.Model.Sugar Forms.ExampleForms.Outputs

def summary
  {Γ : Context}
  (table : InputRef Γ (List RowOutput))
  : Component Γ (List (Item String)) String :=
  let text : Computation Γ (List (Item String)) String := {
    inputs := inputs[.ui table]
    run := fun rows => String.intercalate ", " ((rows.filter (·.selected)).map (·.description)) }
  .withOutput (.computed "Selected descriptions" text) text

def summaryAbove : Layout [0, 0] :=
  .group (some "Selected items") [.place .here, .place (.there .here)]

def tableAbove : Layout [0, 0] :=
  .group (some "Selected items") [.place (.there .here), .place .here]

/-- Owns the table and its summary; `arrangement` only decides where they appear. -/
def tableSummary
  (arrangement : Layout [0, 0] := summaryAbove)
  : Component [] (List (Item String)) String := named%
  present%
    own% table := selectionTable;
    own% summary := summary ref[table];
    .layout { inputs := inputs[ref[summary]], run := id } (.const arrangement)

def pane
  {Γ : Context}
  (shared : Var Γ Nat)
  (name : String)
  : Component Γ Nat := named%[shared]
  state% own := (0 : Nat);
  .group name [
    .computed "Shared count" { inputs := inputs[ref[shared]], run := toString },
    .computed "Private count" { inputs := inputs[ref[own]], run := toString },
    .button "Increment shared" (.set ref[shared] {
      inputs := inputs[ref[shared]], run := fun count => count + 1 }),
    .button "Increment private" (.set ref[own] {
      inputs := inputs[ref[own]], run := fun count => count + 1 })]

def sharedTabs : Component [] Nat Nat := named%
  present%
    state% shared := (0 : Nat);
    tabs% active, strip := "Panes", #v["First pane", "Second pane"];
    own% first := pane ref[shared] "First pane";
    own% second := pane ref[shared] "Second pane";
    .layout { inputs := inputs[ref[shared]], run := id } {
      inputs := inputs[ref[active]]
      run := fun active => .group (some "Shared state across tabs") [
        .place slot[strip],
        #v[.place slot[first], .place slot[second]][active]] }

/-- A presentation inside each list row, with row-local tab state. -/
def noteTabs {Γ : Context} : Component Γ String := named%
  present%
    tabs% active, strip := "Note view", #v["Edit", "Preview"];
    own% edit := .field .self "Text" .text;
    own% preview := .computed "Preview" {
      inputs := inputs[path[]], run := fun text => s!"«{text}»" };
    .arrange {
      inputs := inputs[ref[active]]
      run := fun active => .group none [
        .place slot[strip],
        #v[.place slot[edit], .place slot[preview]][active]] }

/-- An outer presentation that owns rows with their own presentations. -/
def notes : Component [] (List (Item String)) Nat := named%
  present%
    own% list := Component.void (.list .self "Notes" (.numbered "Note") "Add note"
      (Item.mkWithoutUuid "")
      (.zoom path[Item.Field.value] noteTabs));
    own% count := .computed "Note count" {
      inputs := inputs[path[]], run := fun notes => toString notes.length };
    .layout { inputs := inputs[path[]], run := List.length }
      (.const (.group none [.place slot[count], .place slot[list]]))

def initialNotes : List (Item String) := IdGen.run (["First note", "Second note"].mapM Item.fresh)

end Forms.ExampleForms.Presentation
