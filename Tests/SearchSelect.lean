module

public import Forms.ExampleForms.Registry
public import Tests.FreshId
public import Tests.Fetch

public section
namespace Tests.SearchSelect
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private abbrev State := ModelForm.State Delivery.form

private def execute (state : State) (input : ModelForm.Event Delivery.Raw) : IO State :=
  IO.ofExcept (ModelForm.execute (model := Delivery) Delivery.form state input)

private def control? (state : State) (label : String) : Option Display.Control :=
  (ModelForm.snapshot Delivery.form state).controls.find? (·.label == label)

private def control (state : State) (label : String) : IO Display.Control := do
  let some control := control? state label | throw (IO.userError s!"FAIL no control {label}")
  return control

private def apply (state : State) (label : String) (argument : Option Input) : IO State := do
  execute state (.apply (← control state label).key argument)

private def settle (state : State) : IO State :=
  (state.outbox.filterMap fun
    | .fetch fetch => some fetch.request
    | .submit => none
    | .focus _ => none).foldlM (init := state) fun state request => do
    execute state (.loaded (← pendingFetch state request)
      ((Delivery.serve request).elim (.error "Not found.") .ok))

private def editor (state : State) : IO Display.Editor :=
  return (← control state "Country (composed)").input

private def shown (state : State) : IO String := do
  match ← editor state with
  | .choice shown _ => return shown
  | .field ..
  | .lookup ..
  | .action
  | .tabs .. => throw (IO.userError "FAIL composed country is no choice")

private def options (state : State) : IO (List Display.SelectableOption) := do
  match ← editor state with
  | .choice _ options => return options
  | .field ..
  | .lookup ..
  | .action
  | .tabs .. => throw (IO.userError "FAIL composed country is no choice")

private def search (state : State) (text : String) : IO State := do
  settle (← apply state "Search countries" (some (.text text)))

private def germany : Reference Country := ⟨.germany, "Germany"⟩

private def labels (references : List (Reference String)) : List String :=
  let results := (LookupResults.ofList (references.map LookupCandidate.ofReference) false).toOption
  (results.map fun results => (SearchChoices.of results none).options.options.map (·.label)).getD []

def run : IO Unit := do
  let definition := FormDefinition.ofModel Delivery Delivery.form Delivery.initial
  let (opened, _) ← IO.ofExcept (definition.openState (toJson Delivery.initial) supply)
  let opened : State ← settle opened
  check "SearchSelectListsOnOpen"
    ((← options opened).map (·.label) == ["Austria", "Belgium", "Germany", "Catalonia", "France"])
  let found ← search opened "an"
  check "SearchSelectFilters"
    ((← options found).map (·.label) == ["Germany", "France", "Netherlands", "Switzerland"])
  let some germanyOption := (← options found).find? (·.label == "Germany")
    | throw (IO.userError "FAIL germany not listed")
  let chosen ← apply found "Country (composed)" (some (.text germanyOption.value))
  check "SearchSelectChooseStores" (chosen.value.country == some germany)
  check "SearchSelectSharesValueWithLookup"
    (match (← control chosen "Country").input with
      | .lookup picked _ => picked.map (·.label) == some "Germany"
      | .field ..
      | .choice ..
      | .action
      | .tabs .. => false)
  let other ← search chosen "cat"
  check "SearchSelectKeepsChosenWhileSearching"
    (other.value.country == some germany && (← shown other) == germanyOption.value &&
      (← options other).map (·.label) == ["Germany", "Catalonia"])
  let cleared ← apply other "Clear" none
  check "SearchSelectClear" (cleared.value.country.isNone && (control? cleared "Clear").isNone)
  check "SearchSelectSuffixesRepeatedLabels"
    (labels [⟨"GE", "Georgia"⟩, ⟨"US-GA", "Georgia"⟩, ⟨"ES", "Spain"⟩] ==
      ["Georgia (GE)", "Georgia (US-GA)", "Spain"])
  check "SearchSelectFallsBackToKeys"
    (labels [⟨"x", "Acme (1)"⟩, ⟨"1", "Acme"⟩, ⟨"2", "Acme"⟩] ==
      ["\"x\"", "\"1\"", "\"2\""])

end Tests.SearchSelect
