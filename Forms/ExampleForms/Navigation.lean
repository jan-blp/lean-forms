module

public import Forms.ExampleForms.Person

@[expose] public section
namespace Forms.ExampleForms.Navigation
open Forms.Model

def form : Component [] Person.Raw (List Issue) :=
  .present <|
    .tabs "Sections" #v["Person", "Address"] <|
      .own .issues <|
        .own (.focus (.const (some (.ofPath path[Person.Field.address]))) .issues) <|
          let active : Var _ (Fin 2) := .there (.there (.there .here))
          let issues : Computation _ Person.Raw (List Issue) := {
            inputs := inputs[.ui (Ref.there Ref.here)], run := id }
          let address : Computation _ Person.Raw (List Issue) := {
            inputs := inputs[.ui (Ref.here : InputRef _ (Option (List Issue)))]
            run := (·.getD []) }
          .own (.group "Problems" [
            .computed "Current issues" ((fun issues =>
              String.intercalate "\n" (issues.map (·.message))) <$> issues),
            .disabledWhen (List.isEmpty <$> address) <|
              .button "Go to address problem"
                (.set active (.const 1) ++
                  .visit ((fun issues => issues.head?.bind (·.destination?)) <$> address))]) <|
            .own (.group "Person" [
              .field path[Person.Field.name] "Name" .text,
              .field path[Person.Field.age] "Age" .natural]) <|
              .own (.field path[Person.Field.address, Address.Field.street] "Street" .text) <|
                let shift : Renaming _ _ := fun ref => .there (.there (.there ref))
                .layout (issues.rename shift)
                  { inputs := inputs[.ui (shift active)]
                    run := fun tab => .group (some "Navigable person") [
                      .place (.there (.there .here)),
                      .place (.there (.there (.there (.there (.there .here))))),
                      .place (if tab.val == 0 then .there .here else .here)] }

def initial : Person.Raw := { Person.initial with address := ⟨""⟩ }

end Forms.ExampleForms.Navigation
