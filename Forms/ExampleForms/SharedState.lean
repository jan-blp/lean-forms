module

public import Forms.Model.Component

@[expose] public section
namespace Forms.ExampleForms.SharedState
open Forms.Model

def consumer
  {Γ : Context}
  (shared : Var Γ Nat)
  : Component Γ Nat :=
  .bind (0 : Nat) <|
    let own : Var (⟨.writable, Nat⟩ :: Γ) Nat := .here
    let shared := shared.there
    .group "" [
      .computed "Item" { inputs := inputs[path[]], run := toString },
      .computed "Shared count" { inputs := inputs[.ui shared], run := toString },
      .computed "Private count" { inputs := inputs[.ui own], run := toString },
      .button "Increment shared" (.set shared {
        inputs := inputs[.ui shared], run := fun count => count + 1 }),
      .button "Increment private" (.set own {
        inputs := inputs[.ui own], run := fun count => count + 1 })]

def form : Component [] (List Nat) :=
  .bind (0 : Nat) <|
    let shared : Var [⟨.writable, Nat⟩] Nat := .here
    .group "Shared local state" [
      Component.void <| .list .self "Consumers" "Consumer" 0 (consumer shared),
      .computed "Shared count outside the list" { inputs := inputs[.ui shared], run := toString },
      .button "Clear shared" (.set shared (.const 0))]

def initial : List Nat := [10, 20]

end Forms.ExampleForms.SharedState
