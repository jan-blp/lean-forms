module

public import Forms
public import Forms.ExampleForms.SharedState
public import Forms.ExampleForms.Presentation
import Tests.Sugar.Diagnostics
import Tests.Sugar.Parsing
import Tests.Sugar.TabInference

@[expose] public section
namespace Tests.Sugar
open Forms.Model Forms.Model.Sugar Forms.Runtime

def counter {Γ : Context} : Component Γ Nat Nat := named%
  state% count := (0 : Nat);
  state% expanded := false;
  .withOutput
    (.group "Counter" [
      .computed "Count" { inputs := inputs[.ui ref[count]], run := toString },
      .button "Increment" (.set ref[count] {
        inputs := inputs[.ui ref[count]], run := fun n => n + 1 }),
      .button "Toggle" (.set ref[expanded] {
        inputs := inputs[.ui ref[expanded]], run := Bool.not })])
    { inputs := inputs[.ui ref[count]], run := id }

def explicitCounter {Γ : Context} : Component Γ Nat Nat :=
  .bind (0 : Nat) <|
    .bind false <|
      .withOutput
        (.group "Counter" [
          .computed "Count" { inputs := inputs[.ui (.there .here)], run := toString },
          .button "Increment" (.set (.there .here) {
            inputs := inputs[.ui (.there .here)], run := fun n => n + 1 }),
          .button "Toggle" (.set .here {
            inputs := inputs[.ui .here], run := Bool.not })])
        { inputs := inputs[.ui (.there .here)], run := id }

example {Γ : Context} : counter (Γ := Γ) = explicitCounter := rfl

def consumer
  {Γ : Context}
  (shared : Var Γ Nat)
  : Component Γ Nat := named%[shared]
  state% own := (0 : Nat);
  .group "" [
    .computed "Item" { inputs := inputs[path[]], run := toString },
    .computed "Shared count" { inputs := inputs[.ui ref[shared]], run := toString },
    .computed "Private count" { inputs := inputs[.ui ref[own]], run := toString },
    .button "Increment shared" (.set ref[shared] {
      inputs := inputs[.ui ref[shared]], run := fun count => count + 1 }),
    .button "Increment private" (.set ref[own] {
      inputs := inputs[.ui ref[own]], run := fun count => count + 1 })]

example {Γ : Context} (shared : Var Γ Nat) :
    consumer shared = Forms.ExampleForms.SharedState.consumer shared := rfl

def sharedForm : Component [] (List (Item Nat)) := named%
  state% shared := (0 : Nat);
  .group "Shared local state" [
    Component.void <| .list .self "Consumers" (.numbered "Consumer") "Add consumer"
        (Item.mkWithoutUuid 0) (.zoom path[Item.Field.value] (consumer ref[shared])),
    .computed "Shared count outside the list" {
      inputs := inputs[.ui ref[shared]], run := toString },
    .button "Clear shared" (.set ref[shared] (.const 0))]

example : sharedForm = Forms.ExampleForms.SharedState.form := rfl

def tableSummary : Component [] (List (Item String)) String := named%
  present%
    own% table := Forms.ExampleForms.Outputs.selectionTable;
    own% summary := Forms.ExampleForms.Presentation.summary ref[table];
    .layout { inputs := inputs[.ui ref[summary]], run := id }
      (.const (.group (some "Selected items") [.place slot[summary], .place slot[table]]))

example : tableSummary = Forms.ExampleForms.Presentation.tableSummary := rfl

def sharedTabs : Component [] Nat Nat := named%
  present%
    state% shared := (0 : Nat);
    tabs% active, strip := "Panes", #v["First pane", "Second pane"];
    own% first := Forms.ExampleForms.Presentation.pane ref[shared] "First pane";
    own% second := Forms.ExampleForms.Presentation.pane ref[shared] "Second pane";
    .layout { inputs := inputs[.ui ref[shared]], run := id } {
      inputs := inputs[.ui ref[active]]
      run := fun active => .group (some "Shared state across tabs") [
        .place slot[strip],
        #v[.place slot[first], .place slot[second]][active]] }

example : sharedTabs = Forms.ExampleForms.Presentation.sharedTabs := rfl

def importedPair
  {Γ : Context}
  (first : Var Γ Nat)
  (second : Var Γ Nat)
  : Component Γ Nat Nat := named%[first, second]
  state% own := (30 : Nat);
  .output {
    inputs := inputs[.ui ref[first], .ui ref[second], .ui ref[own]]
    run := fun a b c => 100 * a + 10 * b + c }

def reused : Component [] Nat Nat := named%
  state% first := (10 : Nat);
  state% second := (20 : Nat);
  importedPair ref[first] ref[second]

example : (reused.evaluate 0 Env.nil).output = 1230 := by decide

def nestedPresentation : Component [] Nat Nat := named%
  present%
    state% shared := (7 : Nat);
    own% outer := .computed "Outer" "outside";
    own% nested := present%
      own% inner := .computed "Inner" { inputs := inputs[.ui ref[shared]], run := toString };
      .layout { inputs := inputs[.ui ref[shared]], run := id } (.const (.place slot[inner]));
    .layout { inputs := inputs[.ui ref[nested]], run := id } (.const (.place slot[nested]))

example : (nestedPresentation.evaluate 0 Env.nil).output = 7 := by decide

def rows : Component [] (List (Item Nat)) (List Nat) := named%
  state% shared := (7 : Nat);
  .list .self "Rows"
    (row% current, removed => {
      inputs := inputs[.ui ref[shared], .ui ref[current]]
      run := fun shared row => s!"Row {row.index.val + 1} ({shared})" })
    "Add row" (Item.mkWithoutUuid 0)
    (.zoom path[Item.Field.value] <|
      state% own := (3 : Nat);
      .output {
        inputs := inputs[.ui ref[shared], .ui ref[own], path[]]
        run := fun shared own value => shared + own + value })

def explicitRows : Component [] (List (Item Nat)) (List Nat) :=
  .bind (7 : Nat) <|
    .list .self "Rows"
      { inputs := inputs[.ui (.there (.there .here)), .ui Ref.row]
        run := fun shared row => s!"Row {row.index.val + 1} ({shared})" }
      "Add row" (Item.mkWithoutUuid 0)
      (.zoom path[Item.Field.value] <|
        .bind (3 : Nat) <|
          .output {
            inputs := inputs[.ui (.there .here), .ui .here, path[]]
            run := fun shared own value => shared + own + value })

example : rows = explicitRows := rfl

def independentNames : Component [] Nat Nat := named%
  let first : Component [] Nat Nat := named%
    state% count := (10 : Nat);
    .output { inputs := inputs[.ui ref[count]], run := id }
  let second : Component [] Nat Nat := named%
    state% count := (20 : Nat);
    .output { inputs := inputs[.ui ref[count]], run := id }
  .sequence (Component.void first) second

example : (independentNames.evaluate 0 Env.nil).output = 20 := by decide

def stateBetweenOwners : Component [] Nat Nat := named%
  present%
    own% producer := .output (.const (7 : Nat));
    state% ignored := false;
    own% display := .computed "Count" { inputs := inputs[.ui ref[producer]], run := toString };
    .layout { inputs := inputs[.ui ref[producer]], run := id }
      (.const (.group none [.place slot[producer], .place slot[display]]))

example : stateBetweenOwners =
    (Component.present <|
      .own (.output (.const (7 : Nat))) <|
        .bind false <|
          .own (.computed "Count" { inputs := inputs[.ui (.there .here)], run := toString }) <|
            .layout { inputs := inputs[.ui (.there (.there .here))], run := id }
              (.const (.group none [.place (.there .here), .place .here]))) := rfl

def dynamicTabs : Component [] Nat Nat := named%
  present%
    tabs% active, strip := "Dynamic", {
      inputs := inputs[.ui ref[active]]
      run := fun active => if active.val == 0 then #v["First", "Second"] else #v["One", "Two"] };
    .layout { inputs := inputs[.ui ref[active]], run := Fin.val } (.const (.place slot[strip]))

example : (dynamicTabs.evaluate 0 Env.nil).output = 0 := by decide

def tabNames : Vector String 2 := #v["Edit", "Preview"]

def parenthesizedTabs : Component [] Nat Nat := named%
  present%
    tabs% active, strip := "View", (#v["Edit", "Preview"]);
    own% edit := .computed "Edit" "editing";
    own% preview := .computed "Preview" "previewing";
    .layout { inputs := inputs[.ui ref[active]], run := Fin.val } {
      inputs := inputs[.ui ref[active]]
      run := fun active => .group none [
        .place slot[strip],
        #v[.place slot[edit], .place slot[preview]][active]] }

def definedTabs : Component [] Nat Nat := named%
  present%
    tabs% active, strip := "View", tabNames;
    own% edit := .computed "Edit" "editing";
    own% preview := .computed "Preview" "previewing";
    .layout { inputs := inputs[.ui ref[active]], run := Fin.val } {
      inputs := inputs[.ui ref[active]]
      run := fun active => .group none [
        .place slot[strip],
        #v[.place slot[edit], .place slot[preview]][active]] }

example : parenthesizedTabs = definedTabs := rfl

def displayTabs : Display.Editor := named% .tabs 0 ["Edit", "Preview"]

example : displayTabs = Display.Editor.tabs 0 ["Edit", "Preview"] := rfl

def hygienic : Component [] Nat Nat := named%
  state% count := (10 : Nat);
  let count := 99
  .output { inputs := inputs[.ui ref[count]], run := fun value => value + count }

example : (hygienic.evaluate 0 Env.nil).output = 109 := by decide

public meta def quotedReference : Lean.MacroM (Lean.TSyntax `term) := named%
  `(ref[missing])

namespace ImportHygiene

def reference : Var [⟨.writable, Nat⟩, ⟨.writable, Nat⟩] Nat := .there .here

macro "named_import_hygiene%" : term =>
  `(named%[reference] .output { inputs := inputs[.ui ref[reference]], run := id })

end ImportHygiene

def importedHygiene : Component [⟨.writable, Nat⟩, ⟨.writable, Nat⟩] Nat Nat :=
  let reference : Var [⟨.writable, Nat⟩, ⟨.writable, Nat⟩] Nat := .here
  let _ := reference
  named_import_hygiene%

example : (importedHygiene.evaluate 0 env[10, 20]).output = 20 := by decide

end Tests.Sugar
