module

public import Forms.ExampleForms.Person
public import Forms.Model.Sugar

@[expose] public section
namespace Forms.ExampleForms.Navigation
open Forms.Model Forms.Model.Sugar

def form : Component [] Person.Raw (List Issue) := named%
  present%
    tabs% active, sections := "Sections", #v["Person", "Address"];
    own% issues := .issues;
    own% addressIssues := .zoom? (.const (some (.ofPath path[Person.Field.address]))) .issues;
    own% problems :=
      let address : Computation _ Person.Raw (List Issue) := {
        inputs := inputs[.ui ref[addressIssues]], run := (·.getD []) }
      .group "Problems" [
        .computed "Current issues" {
          inputs := inputs[.ui ref[issues]]
          run := fun issues => String.intercalate "\n" (issues.map (·.message)) },
        .disabledWhen (List.isEmpty <$> address) <|
          .button "Go to address problem"
            (.set ref[active] (.const 1) ++
              .visit ((fun issues => issues.head?.bind (·.destination?)) <$> address))];
    own% person := .group "Person" [
      .field path[Person.Field.name] "Name" .text,
      .field path[Person.Field.age] "Age" .natural];
    own% street := .field path[Person.Field.address, Address.Field.street] "Street" .text;
    .layout { inputs := inputs[.ui ref[issues]], run := id }
      { inputs := inputs[.ui ref[active]]
        run := fun tab => .group (some "Navigable person") [
          .place slot[problems],
          .place slot[sections],
          .place (if tab.val == 0 then slot[person] else slot[street])] }

def initial : Person.Raw := { Person.initial with address := ⟨""⟩ }

end Forms.ExampleForms.Navigation
