module

public import Forms.ExampleForms.Outputs

@[expose] public section
namespace Forms.ExampleForms.Presentation
open Forms.Model Forms.ExampleForms.Outputs

def summary
  {Γ : Context}
  (table : InputRef Γ (List RowOutput))
  : Component Γ (List String) String :=
  let text : Computation Γ (List String) String := {
    inputs := inputs[.ui table]
    run := fun rows => String.intercalate ", " ((rows.filter (·.selected)).map (·.description)) }
  .withOutput (.computed "Selected descriptions" text) text

def summaryAbove : Layout 2 := .group (some "Selected items") [.place .here, .place (.there .here)]

def tableAbove : Layout 2 := .group (some "Selected items") [.place (.there .here), .place .here]

/-- Owns the table and its summary; `arrangement` only decides where they appear. -/
def tableSummary (arrangement : Layout 2 := summaryAbove) : Component [] (List String) String :=
  .present <|
    .own selectionTable <|
      .own (summary .here) <|
        .layout { inputs := inputs[.ui (Ref.here : InputRef _ String)], run := id } (.const arrangement)

def pane
  {Γ : Context}
  (shared : Var Γ Nat)
  (name : String)
  : Component Γ Nat :=
  .bind (0 : Nat) <|
    let own : Var (⟨.writable, Nat⟩ :: Γ) Nat := .here
    let shared := shared.there
    .group name [
      .computed "Shared count" { inputs := inputs[.ui shared], run := toString },
      .computed "Private count" { inputs := inputs[.ui own], run := toString },
      .button "Increment shared" (.set shared {
        inputs := inputs[.ui shared], run := fun count => count + 1 }),
      .button "Increment private" (.set own {
        inputs := inputs[.ui own], run := fun count => count + 1 })]

def sharedTabs : Component [] Nat Nat :=
  .present <|
    .bind (0 : Nat) <|
      .bind (0 : Nat) <|
        let shared : Var [⟨.writable, Nat⟩, ⟨.writable, Nat⟩] Nat := .there .here
        let active : Var [⟨.writable, Nat⟩, ⟨.writable, Nat⟩] Nat := .here
        .own (.tabBar "Panes" active ["First pane", "Second pane"]) <|
          .own (pane shared.there "First pane") <|
            .own (pane shared.there.there "Second pane") <|
              let shared := shared.there.there.there
              let active := active.there.there.there
              .layout { inputs := inputs[.ui shared], run := id } {
                inputs := inputs[.ui active]
                run := fun active => .group (some "Shared state across tabs") [
                  .place (.there (.there .here)),
                  .tabs active [.place (.there .here), .place .here]] }

/-- A presentation inside each list row, with row-local tab state. -/
def noteTabs {Γ : Context} : Component Γ String :=
  .present <|
    .bind (0 : Nat) <|
      let active : Var (⟨.writable, Nat⟩ :: Γ) Nat := .here
      .own (.tabBar "Note view" active ["Edit", "Preview"]) <|
        .own (.field .self "Text" .text) <|
          .own (.computed "Preview" { inputs := inputs[path[]], run := fun text => s!"«{text}»" }) <|
            .arrange {
              inputs := inputs[.ui active.there.there.there]
              run := fun active => .group none [
                .place (.there (.there .here)),
                .tabs active [.place (.there .here), .place .here]] }

/-- An outer presentation that owns rows with their own presentations. -/
def notes : Component [] (List String) Nat :=
  .present <|
    .own (Component.void (.list .self "Notes" "Note" "" noteTabs)) <|
      .own (.computed "Note count" { inputs := inputs[path[]], run := fun notes => toString notes.length }) <|
        .layout { inputs := inputs[path[]], run := List.length }
          (.const (.group none [.place .here, .place (.there .here)]))

end Forms.ExampleForms.Presentation
