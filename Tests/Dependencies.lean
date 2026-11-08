module

public import Forms.Model.Computation
public import Tests.FormModel

@[expose] public section
namespace Tests.Dependencies
open Forms.Model Tests.FormModel

def visible : Computation Person.Raw Bool :=
  .of (inputs[.field Person.Field.age .self, .field Person.Field.subscribed .self])
    (fun age subscribed => subscribed && age ≥ 18)

def disabled : Computation Person.Raw Bool :=
  .of (inputs[.field Person.Field.age .self]) (fun age => decide (age > 120))

def summary : Computation Person.Raw String :=
  .of (inputs[.field Person.Field.address (.field Address.Field.street .self), .field Person.Field.age .self])
    (fun street age => s!"{street}: {age}")

def whole : Computation Delivery.Raw String :=
  .of (inputs[.self]) fun
    | .pickup => "Pickup"
    | .home payload => payload.instructions
    | .campus payload => s!"Campus: {payload.age}"

def campusAge : Computation Delivery.campus.Raw Nat :=
  .of (inputs[.field Delivery.campus.Field.age .self]) (fun age => age + 1)

def run : IO Unit := do
  let person : Person.Raw := ⟨⟨"Campus"⟩, 20, true⟩
  check "DependenciesSelectHeterogeneousInputs" (visible.eval person == true)
  check "DependenciesReactToSelectedField" (visible.eval (Person.Field.age.set 16 person) == false)
  check "DependenciesReactToSecondSelectedField"
    (visible.eval (Person.Field.subscribed.set false person) == false)
  check "DependenciesIgnoreUnselectedField"
    (visible.eval (Person.Field.address.set ⟨"Road"⟩ person) == visible.eval person)
  check "DependenciesDisabledRule" (disabled.eval (Person.Field.age.set 150 person) == true)
  check "DependenciesReadNestedFields" (summary.eval person == "Campus: 20")
  check "DependenciesWholeModel" (whole.eval .pickup == "Pickup" && whole.eval (.campus ⟨20⟩) == "Campus: 20")
  check "DependenciesConstructorPayload" (campusAge.eval ⟨20⟩ == 21)
  let renderBranch : Delivery.Raw → Nat
    | .campus payload => campusAge.eval payload
    | _ => 0
  check "DependenciesConstructorSelectionOutsidePaths"
    (renderBranch .pickup == 0 && renderBranch (.campus ⟨20⟩) == 21)
  let constant : Computation Person.Raw String := .of (inputs[]) "Hello"
  check "DependenciesConstant" (constant.eval person == "Hello")
  let street : Computation Address.Raw String :=
    .of (inputs[.field Address.Field.street .self]) (fun street => street ++ "!")
  let embedded := street.weaken (.field Person.Field.address .self)
  check "DependenciesComposeWhenEmbedded" (embedded.eval person == street.eval person.address)

end Tests.Dependencies
