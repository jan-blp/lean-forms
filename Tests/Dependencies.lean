module

public import Forms.Model.Computation
public import Forms.Model.RowSelection
public import Tests.FormModel

@[expose] public section
namespace Tests.Dependencies
open Forms.Model Tests.FormModel

def visible : Computation [] Person.Raw Bool :=
  .mk (inputs[path[Person.Field.age], path[Person.Field.subscribed]])
    (fun age subscribed => subscribed && age ≥ 18)

def disabled : Computation [] Person.Raw Bool :=
  .mk (inputs[path[Person.Field.age]]) (fun age => decide (age > 120))

def summary : Computation [] Person.Raw String :=
  .mk (inputs[path[Person.Field.address, Address.Field.street], path[Person.Field.age]])
    (fun street age => s!"{street}: {age}")

def whole : Computation [] Delivery.Raw String :=
  .mk (inputs[path[]]) fun
    | .pickup => "Pickup"
    | .home payload => payload.instructions
    | .campus payload => s!"Campus: {payload.age}"

def campusAge : Computation [] Delivery.campus.Raw Nat :=
  .mk (inputs[path[Delivery.campus.Field.age]]) (fun age => age + 1)

def run : IO Unit := do
  let person : Person.Raw := ⟨⟨"Campus"⟩, 20, true⟩
  check "DependenciesSelectHeterogeneousInputs" (visible.eval person Env.nil == true)
  check "DependenciesReactToSelectedField" (visible.eval (Person.Field.age.set 16 person) Env.nil == false)
  check "DependenciesReactToSecondSelectedField"
    (visible.eval (Person.Field.subscribed.set false person) Env.nil == false)
  check "DependenciesIgnoreUnselectedField"
    (visible.eval (Person.Field.address.set ⟨"Road"⟩ person) Env.nil == visible.eval person Env.nil)
  check "DependenciesDisabledRule" (disabled.eval (Person.Field.age.set 150 person) Env.nil == true)
  check "DependenciesReadNestedFields" (summary.eval person Env.nil == "Campus: 20")
  check "DependenciesWholeModel" (whole.eval .pickup Env.nil == "Pickup" && whole.eval (.campus ⟨20⟩) Env.nil == "Campus: 20")
  check "DependenciesConstructorPayload" (campusAge.eval ⟨20⟩ Env.nil == 21)
  let renderBranch : Delivery.Raw → Nat
    | .campus payload => campusAge.eval payload Env.nil
    | _ => 0
  check "DependenciesConstructorSelectionOutsidePaths"
    (renderBranch .pickup == 0 && renderBranch (.campus ⟨20⟩) == 21)
  let constant : Computation [] Person.Raw String := .mk (inputs[]) "Hello"
  check "DependenciesConstant" (constant.eval person Env.nil == "Hello")
  let street : Computation [] Address.Raw String :=
    .mk (inputs[path[Address.Field.street]]) (fun street => street ++ "!")
  let embedded := street.weaken (path[Person.Field.address])
  check "DependenciesComposeWhenEmbedded" (embedded.eval person Env.nil == street.eval person.address Env.nil)
  let selection : Var [⟨.writable, RowSelection⟩, ⟨.writable, RowSelection⟩] RowSelection := .here
  let other : Var [⟨.writable, RowSelection⟩, ⟨.writable, RowSelection⟩] RowSelection := .there .here
  let ui : Env [⟨.writable, RowSelection⟩, ⟨.writable, RowSelection⟩] := env[.row 1, .none]
  let initial : Env [⟨.writable, RowSelection⟩, ⟨.writable, RowSelection⟩] := env[.none, .none]
  let selectedStreet : Computation [⟨.writable, RowSelection⟩, ⟨.writable, RowSelection⟩] Address.Raw String :=
    .mk (inputs[path[Address.Field.street], .ui selection]) fun street selected =>
      if selected == .row 1 then street else "Nothing selected"
  let selectedEmbedded := selectedStreet.weaken path[Person.Field.address]
  check "DependenciesReadModelAndUi"
    (selectedStreet.eval person.address ui == "Campus" &&
      selectedStreet.eval person.address initial == "Nothing selected")
  check "DependenciesWeakenKeepsSharedUi"
    (selectedEmbedded.eval person ui == selectedStreet.eval person.address ui)
  let readSelection : Computation [⟨.writable, RowSelection⟩, ⟨.writable, RowSelection⟩] Nat RowSelection :=
    .mk (inputs[.ui selection]) id
  check "DependenciesSelectionIndependentOfModelType" (readSelection.eval 42 ui == .row 1)
  check "DependenciesVariablesIndependent" (other.get ui == .none)
  let expanded : Var [⟨.writable, Bool⟩, ⟨.writable, String⟩] Bool := .here
  let filter : Var [⟨.writable, Bool⟩, ⟨.writable, String⟩] String := .there .here
  let genericUi : Env [⟨.writable, Bool⟩, ⟨.writable, String⟩] := env[true, "hotel"]
  let initialUi : Env [⟨.writable, Bool⟩, ⟨.writable, String⟩] := env[false, ""]
  let visibleFilter : Computation [⟨.writable, Bool⟩, ⟨.writable, String⟩] Nat String :=
    .mk (inputs[.ui expanded, .ui filter]) fun isExpanded text => if isExpanded then text else "hidden"
  check "DependenciesReadGenericUiValues"
    (visibleFilter.eval 42 genericUi == "hotel" && visibleFilter.eval 42 initialUi == "hidden")
  check "DependenciesVariablesUpdateIndependently"
    (expanded.get (filter.set "hotel" initialUi) == false &&
      filter.get (expanded.set true initialUi) == "")

end Tests.Dependencies
