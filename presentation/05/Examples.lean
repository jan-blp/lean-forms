module

public import Forms.ExampleForms.Order
public import Forms.ExampleForms.SharedState
public import Forms.ExampleForms.Presentation

@[expose] public section
namespace Forms.Presentation.Composition
open Forms.Model Forms.Model.Sugar Forms.ExampleForms

namespace Lambda

inductive Term : List Type → Type → Type 1 where
  | var (ref : Member α Γ) : Term Γ α
  | lam (body : Term (α :: Γ) β) : Term Γ (α → β)
  | app (fn : Term Γ (α → β)) (arg : Term Γ α) : Term Γ β

def first : Term [] (Nat → Bool → Nat) :=
  .lam (.lam (.var (.there .here)))

end Lambda

def orderTotal : Computation [] Order.Raw Nat :=
  compute%
    (quantity : Nat) ← path[Order.Field.quantity],
    (price : Nat) ← path[Order.Field.unitPrice] =>
    quantity * price

def clicks {Γ : Context} : Component Γ Nat Unit 0 :=
  .bind (0 : Nat) <|
    .group "Counter" [
      .field .self "Value" .natural,
      .computed "Clicks"
        (compute% (value : Nat) ← .ui .here =>
          toString value),
      .button "Increment" (.set .here
        (compute% (n : Nat) ← .ui .here =>
          n + 1))]

def twoCounters : Component [] Nat Unit 0 :=
  .group "Two counters" [clicks, clicks]

def counterView
  {Γ : Context}
  (count : Var Γ Nat)
  (expanded : Var Γ Bool)
  : Component Γ Nat Unit 0 :=
  .group "Counter" [
    .field .self "Value" .natural,
    .computed "Clicks"
      (compute% (value : Nat) ← .ui count =>
        toString value),
    .button "Increment" (.set count
      (compute% (n : Nat) ← .ui count =>
        n + 1)),
    .button "Toggle details" (.set expanded
      (compute% (value : Bool) ← .ui expanded =>
        !value)),
    .visibleWhen
      (compute% value ← .ui expanded =>
        value)
      (.computed "Details" "This counter has its own state.")]

def counter {Γ : Context} : Component Γ Nat Nat 0 :=
  .bind (0 : Nat) <|
    .bind false <|
      .withOutput
        (counterView (.there .here) .here)
        (compute% value ← .ui (.there .here) =>
          value)

def pair {Γ : Context} : Component Γ Nat Nat 0 :=
  .observe counter <|
    .observe counter <|
      .output
        (compute%
          (first : Nat) ← .ui (.there .here),
          (second : Nat) ← .ui .here =>
          first + second)

def consumer
  {Γ : Context}
  (shared : Var Γ Nat)
  : Component Γ Nat Unit 0 :=
  .bind (0 : Nat) <|
    .group "" [
      .computed "Shared"
        (compute% (value : Nat) ← .ui shared.there =>
          toString value),
      .computed "Private"
        (compute% (value : Nat) ← .ui .here =>
          toString value)]

abbrev exampleContext : Context :=
  [⟨.writable, Bool⟩, ⟨.writable, Nat⟩]

def count : Var exampleContext Nat := .there .here

def values : Env exampleContext := env[false, 7]

example : count.get values = 7 := rfl

def rawState {Γ : Context} : Component Γ Nat Nat 0 :=
  .bind (0 : Nat) <|
    .bind false <|
      .output
        (compute% value ← .ui (.there .here) =>
          value)

def namedState {Γ : Context} : Component Γ Nat Nat 0 := named%
  state% count := (0 : Nat);
  state% _ := false;
  .output
    (compute% value ← ref[count] =>
      value)

example {Γ : Context} : namedState (Γ := Γ) = rawState := rfl

def sum
  {Γ : Context}
  (first second : InputRef Γ Nat)
  : Computation Γ Nat Nat :=
  (compute%
    (first : Nat) ← .ui first,
    (second : Nat) ← .ui second =>
    first + second)

def summaryAbove : Layout [0, 0] :=
  .group (some "Selected items") [.place .here, .place (.there .here)]

def tableAbove : Layout [0, 0] :=
  .group (some "Selected items") [.place (.there .here), .place .here]

def tableSummary (arrangement : Layout [0, 0])
  : Component [] (List (Item String)) String :=
  .present <|
    .own Forms.ExampleForms.Outputs.selectionTable <|
      .own (Forms.ExampleForms.Presentation.summary .here) <|
        .layout
          (compute% value ← .ui (.here : InputRef _ String) =>
            value)
          (compute% =>
            arrangement)

def summaryFirst : Component [] (List (Item String)) String :=
  tableSummary summaryAbove

def tableFirst : Component [] (List (Item String)) String :=
  tableSummary tableAbove

def sharedTabs : Component [] Nat Nat 0 :=
  .present <|
    .bind (0 : Nat) <|
      .tabs "Panes" (compute% =>
        #v["First", "Second"]) <|
        .own (Forms.ExampleForms.Presentation.pane (.there (.there .here)) "First") <|
          .own (Forms.ExampleForms.Presentation.pane (.there (.there (.there .here))) "Second") <|
            .layout
              (compute% value ← .ui (.there (.there (.there (.there .here)))) =>
                value)
              (compute% (active : Fin 2) ← .ui (.there (.there (.there .here))) =>
                .group none [
                  .place (.there (.there .here)),
                  #v[.place (.there .here), .place .here][active]])

def collectionWithFooter
  {Γ : Context}
  {α β : Type}
  (collection : Component Γ α β 1)
  (footer : Component Γ α)
  : Component Γ α β := named%
  present%
    own% rows := collection;
    own% footer := footer.rename Renaming.shift;
    .layout
      (compute% value ← ref[rows] =>
        value)
      (compute% =>
        .fill view[rows] (.cons [.place view[footer]] .nil))

example : (pair.evaluate 0 Env.nil).output = 0 := rfl

namespace Named

def clicks {Γ : Context} : Component Γ Nat Unit 0 := named%
  state% count := (0 : Nat);
  .group "Counter" [
    .field .self "Value" .natural,
    .computed "Clicks"
      (compute%
        (value : Nat) ← ref[count]
        => toString value),
    .button "Increment" (.set ref[count]
      (compute%
        (n : Nat) ← ref[count]
        => n + 1))]

example {Γ : Context} : clicks (Γ := Γ) = Composition.clicks := rfl

def consumer
  {Γ : Context}
  (shared : Ref Γ .writable Nat)
  : Component Γ Nat Unit 0 := named%[shared]
  state% count := (0 : Nat);
  .group "" [
    .computed "Shared"
      (compute%
        (value : Nat) ← ref[shared]
        => toString value),
    .computed "Private"
      (compute%
        (value : Nat) ← ref[count]
        => toString value)]

example {Γ : Context} (shared : Ref Γ .writable Nat) :
    consumer shared = Composition.consumer shared := rfl

def counter {Γ : Context} : Component Γ Nat Nat 0 := named%
  state% count := (0 : Nat);
  .withOutput
    (.group "Counter" [
      .field .self "Value" .natural,
      .computed "Clicks"
        (compute%
          (value : Nat) ← ref[count]
          => toString value),
      .button "Increment" (.set ref[count]
        (compute%
          (n : Nat) ← ref[count]
          => n + 1))])
    (compute%
      value ← ref[count]
      => value)

def pair {Γ : Context} : Component Γ Nat Nat 0 := named%
  observe% first := counter;
  observe% second := counter;
  .output
    (compute%
      (x : Nat) ← ref[first],
      (y : Nat) ← ref[second]
      => x + y)

def collectionWithFooter
  {Γ : Context}
  {α β : Type}
  (collection : Component Γ α β 1)
  (addButton : Component Γ α)
  : Component Γ α β := named%
  present%
    own% rows := collection;
    own% add := addButton.rename Renaming.shift;
    .layout
      (compute%
        value ← ref[rows]
        => value)
      (compute%
        => .fill view[rows] (.cons [.place view[add]] .nil))

def sharedClicks
  {Γ : Context}
  (count : Ref Γ .writable Nat)
  : Component Γ Nat Unit 0 := named%[count]
  .group "Counter" [
    .field .self "Value" .natural,
    .computed "Clicks"
      (compute%
        (value : Nat) ← ref[count]
        => toString value),
    .button "Increment" (.set ref[count]
      (compute%
        (n : Nat) ← ref[count]
        => n + 1))]

def twoShared : Component [] Nat Unit 0 := named%
  state% count := (0 : Nat);
  .group "Two counters" [sharedClicks ref[count], sharedClicks ref[count]]

def row
  {Γ : Context}
  : Component Γ (Item String) (Option String) 0 := named%
  state% selected := false;
  .withOutput
    (.group "" [
      .field path[Item.Field.value] "Description" .text,
      .button "Toggle" (.set ref[selected]
        (compute%
          s ← ref[selected]
          => !s))])
    (compute%
      (description : String) ← path[Item.Field.value],
      (s : Bool) ← ref[selected]
      => if s then some description else none)

def selection : Component [] (List (Item String)) Unit 0 := named%
  observe% (rows : List (Option String)) := .list
    (path := .self)
    (label := "Items")
    (rowLabel := .numbered "Item")
    (addCaption := "Add item")
    (initial := Item.mkWithoutUuid "New item")
    (body := row);
  .computed "Selected"
    (compute%
      (selected : List (Option String)) ← ref[rows]
      => ", ".intercalate (selected.filterMap id))

def items {Γ : Context} : Component Γ (List (Item String)) (List (Option String)) 1 :=
  .collection .self "Items"
    (named%
      presentation%
        own% (item : Option String) := row.rename Renaming.row;
        .layout
          (compute%
            value ← ref[item]
            => value)
          (compute%
            => .place view[item]))
    .list

def summaryInside : Component [] (List (Item String)) Unit 0 := named%
  present%
    own% (rows : List (Option String)) := items;
    own% summary := .computed "Selected"
      (compute%
        (selected : List (Option String)) ← ref[rows]
        => ", ".intercalate (selected.filterMap id));
    .arrange
      (compute%
        => .fill view[rows] (.cons [.place view[summary]] .nil))

def selected
  {Γ : Context}
  (rows : Ref Γ .readOnly (List (Option String)))
  : Component Γ (List (Item String)) Unit 0 := named%[rows]
  .computed "Selected"
    (compute%
      (selected : List (Option String)) ← ref[rows]
      => ", ".intercalate (selected.filterMap id))

def footerNamed : Component [] (List (Item String)) (List (Option String)) 0 := named%
  present%
    own% rows := items;
    own% summary := selected ref[rows];
    .layout
      (compute%
        value ← ref[rows]
        => value)
      (compute%
        => .fill view[rows]
          (.cons [.place view[summary]] .nil))

def footerRaw : Component [] (List (Item String)) (List (Option String)) 0 :=
  .present <|
    .own items <|
      .own (selected .here) <|
        .layout
          (compute%
            value ← .ui (.there .here)
            => value)
          (compute%
            => .fill (.there .here)
              (.cons [.place .here] .nil))

example : footerNamed = footerRaw := rfl

end Named

end Forms.Presentation.Composition
