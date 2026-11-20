module

public import Forms

open Forms.Model Forms.Model.Sugar

namespace Tests.Sugar.TypedBindings

def counter : Component [] Nat Nat := named%
  state% (count : Nat) := 1;
  .output { inputs := inputs[ref[count]], run := id }

example :
    counter =
    (named%
      state% count := (1 : Nat);
      .output { inputs := inputs[ref[count]], run := id }) := rfl

def observer : Component [] Nat Nat := named%
  observe% (count : Nat) := counter;
  .output { inputs := inputs[ref[count]], run := id }

example :
    observer =
    (named%
      observe% count := counter;
      .output { inputs := inputs[ref[count]], run := id }) := rfl

def owner : Component [] Nat Nat := named%
  present%
    own% (count : Nat) := counter;
    .layout { inputs := inputs[ref[count]], run := id } (.const (.place slot[count]))

example :
    owner =
    (named%
      present%
        own% count := counter;
        .layout { inputs := inputs[ref[count]], run := id } (.const (.place slot[count]))) := rfl

def tabs : Component [] String := named%
  present%
    tabs% (active : Fin 2), (bar : Unit) := "View", #v["Edit", "Preview"];
    own% edit := .field .self "Text" .text;
    own% preview := .computed "Preview" { inputs := inputs[path[]], run := id };
    .arrange {
      inputs := inputs[ref[active]]
      run := fun active => .group none [
        .place slot[bar],
        #v[.place slot[edit], .place slot[preview]][active]] }

example :
    tabs =
    (named%
      present%
        tabs% active, bar := "View", #v["Edit", "Preview"];
        own% edit := .field .self "Text" .text;
        own% preview := .computed "Preview" { inputs := inputs[path[]], run := id };
        .arrange {
          inputs := inputs[ref[active]]
          run := fun active => .group none [
            .place slot[bar],
            #v[.place slot[edit], .place slot[preview]][active]] }) := rfl

def rowLabel {Γ : Context} : Computation (Context.row Nat Γ) Nat String := named%
  row% (current : PointedList Nat), (_ : Bool) => {
    inputs := inputs[ref[current]]
    run := fun row => s!"Row {row.index.val + 1}" }

example {Γ : Context} :
    rowLabel (Γ := Γ) =
    (named%
      row% current, _ => {
        inputs := inputs[ref[current]]
        run := fun (row : PointedList Nat) => s!"Row {row.index.val + 1}" }) := rfl

/--
error: Type mismatch
  counter
has type
  Component [] ℕ ℕ
but is expected to have type
  Component [] ℕ Bool
-/
#guard_msgs in
example : Component [] Nat := named%
  observe% (count : Bool) := counter;
  .computed "Count" { inputs := inputs[ref[count]], run := toString }

/--
error: Type mismatch
  "yes"
has type
  String
but is expected to have type
  Bool
-/
#guard_msgs in
example : Component [] Nat := named%
  state% (count : Bool) := "yes";
  .computed "Count" { inputs := inputs[ref[count]], run := toString }

end Tests.Sugar.TypedBindings
