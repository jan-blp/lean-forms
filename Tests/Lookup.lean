module

public import Forms.ExampleForms.Registry
public import Tests.FreshId

public section
namespace Tests.Lookup
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private abbrev State := ModelForm.State Delivery.form

private def execute (state : State) (input : ModelForm.Event Delivery.Raw) : IO State :=
  IO.ofExcept (ModelForm.execute (model := Delivery) Delivery.form state input)

private def snapshot (state : State) : ModelForm.Snapshot Delivery.Raw :=
  ModelForm.snapshot Delivery.form state

private def control (state : State) (label : String) : IO Display.Control := do
  let some control := (snapshot state).controls.find? (·.label == label)
    | throw (IO.userError s!"FAIL no control {label}")
  return control

private def apply (state : State) (label : String) (argument : Input) : IO State := do
  execute state (.apply (← control state label).key (some argument))

private def fetches (state : State) : List HttpRequest :=
  state.outbox.filterMap fun
    | .fetch request => some request
    | .submit => none
    | .focus _ => none

private def settle (state : State) : IO State :=
  (fetches state).foldlM (init := state) fun state request =>
    execute state (.loaded request ((Delivery.serve request).elim (.error "Not found.") .ok))

private def search? (state : State) (label : String) : IO (Option Display.Search) := do
  match (← control state label).input with
  | .lookup _ search => return search
  | .field ..
  | .choice ..
  | .action
  | .tabs .. => throw (IO.userError s!"FAIL {label} is no lookup")

private def picked? (state : State) (label : String) : IO (Option Display.ChoiceOption) := do
  match (← control state label).input with
  | .lookup picked _ => return picked
  | .field ..
  | .choice ..
  | .action
  | .tabs .. => throw (IO.userError s!"FAIL {label} is no lookup")

private def searched (json : Json) : Option (Option String) :=
  match InputProtocol.fromJson json with
  | .ok (.search text) => some text
  | .ok (.choose _)
  | .ok (.text _)
  | .ok (.boolean _)
  | .ok (.texts _)
  | .ok (.pick _)
  | .error _ => none

private def choiceOf (json : Json) : Option (Option String) :=
  match InputProtocol.fromJson json with
  | .ok (.choose key) => some key
  | .ok (.search _)
  | .ok (.text _)
  | .ok (.boolean _)
  | .ok (.texts _)
  | .ok (.pick _)
  | .error _ => none

private def results? (state : State) (label : String) : IO (Option Display.SearchResults) :=
  return (← search? state label).map (·.results)

private def labels : Display.SearchResults → List String
  | .found options _ => options.map (·.label)
  | .loading
  | .failed _ => []

private def countries (text : String) : HttpRequest := Api.request DeliveryEndpoint.countries text

private def germany : Reference String := ⟨"DE", "Germany"⟩

example : (LookupResults.select [germany, germany] (fun _ => true) 1).map (·.found) =
    .error .duplicateKeys := by
  simp [LookupResults.select, LookupResults.ofList, germany, Reference.wireKey, Except.map]

example : (LookupResults.select [germany] (fun _ => true) 1).map (·.found) = .ok [germany] := by
  simp [LookupResults.select, LookupResults.ofList, germany, Reference.wireKey, Except.map]

example : (LookupResults.select [germany] (fun _ => true) 0).map (·.more) = .ok true := by
  simp [LookupResults.select, LookupResults.ofList, germany, Reference.wireKey, Except.map]

def run : IO Unit := do
  check "LookupDuplicateIdsRejected"
    (fromJson? (α := LookupResults String) (Json.mkObj [
      ("found", toJson [germany, { germany with label := "Deutschland" }]),
      ("more", toJson false)]) |>.isOk |> not)
  let definition := FormDefinition.ofModel Delivery Delivery.form Delivery.initial
  let (opened, _) ← IO.ofExcept (definition.openState (toJson Delivery.initial) supply)
  let opened : State := opened
  check "LookupClosedFetchesNothing" (fetches opened).isEmpty
  check "LookupDependentDisabled" (← control opened "City").disabled
  let searching ← apply opened "Country" (.search (some "an"))
  check "LookupSearchFetches" (fetches searching == [countries "an"])
  check "LookupLoadingShown" ((← search? searching "Country") == some ⟨"an", .loading⟩)
  let found ← settle searching
  let some results := (← search? found "Country") | throw (IO.userError "FAIL search closed")
  check "LookupMatchesShown" (labels results.results == ["Germany", "France", "Netherlands"])
  let all ← settle (← apply found "Country" (.search (some "")))
  let allResults ← results? all "Country"
  check "LookupMoreShown" (match allResults with
    | some (.found options more) => options.length == 5 && more
    | some .loading
    | some (.failed _)
    | none => false)
  let unlisted ← apply found "Country" (.choose (some (Reference.wireKey ⟨"IT", "Italy"⟩)))
  check "LookupUnlistedRejected"
    ((snapshot unlisted).ui.rejection == some (toString (InvocationError.unlistedMatch "\"IT\"")))
  let chosen ← apply found "Country" (.choose (some germany.wireKey))
  check "LookupChooseStores" (chosen.value.country == some germany)
  check "LookupChooseCloses" ((← search? chosen "Country").isNone && (fetches chosen).isEmpty)
  let other ← settle (← apply chosen "Country" (.search (some "spa")))
  check "LookupPickedShownWhileSearching"
    ((← picked? other "Country") == some { value := germany.wireKey, label := "Germany" } &&
      ((← search? other "Country").map (labels ·.results)) == some ["Spain"])
  let again ← apply other "Country" (.search (some "an"))
  check "LookupRevisitIsCached" ((fetches again).isEmpty &&
    ((← search? again "Country").map (labels ·.results)) == some ["Germany", "France", "Netherlands"])
  let cities ← apply chosen "City" (.search (some ""))
  check "LookupDependencyInRequest"
    (fetches cities == [Api.request DeliveryEndpoint.cities ({ country := "DE", text := "" } : CitySearch)])
  let cities ← settle cities
  check "LookupDependentMatches"
    (((← search? cities "City").map (labels ·.results)) == some ["Berlin", "Hamburg", "Munich"])
  let berlin : Reference String := { id := "BER", label := "Berlin" }
  let pickedCity ← apply cities "City" (.choose (some berlin.wireKey))
  let searchingCountry ← apply pickedCity "Country" (.search (some "an"))
  check "LookupSearchPreservesDependentValue" (searchingCountry.value.city == some berlin)
  let sameCountry ← apply searchingCountry "Country" (.choose (some germany.wireKey))
  check "LookupSameCountryPreservesCity" (sameCountry.value.city == some berlin)
  let spainResults ← settle (← apply pickedCity "Country" (.search (some "spa")))
  let spain : Reference String := { id := "ES", label := "Spain" }
  let changedCountry ← apply spainResults "Country" (.choose (some spain.wireKey))
  check "LookupCountryChangeClearsCity"
    (changedCountry.value.country == some spain && changedCountry.value.city.isNone)
  let clearedCountry ← apply pickedCity "Country" (.choose none)
  check "LookupCountryClearClearsCity"
    (clearedCountry.value.country.isNone && clearedCountry.value.city.isNone &&
      (← control clearedCountry "City").disabled)
  let stopped ← apply cities "City" (.search none)
  check "LookupStopSearching" ((← search? stopped "City").isNone && stopped.value.city.isNone)
  let cleared ← apply chosen "Country" (.choose none)
  check "LookupClear" cleared.value.country.isNone
  let failed ← execute searching (.loaded (countries "an") (.error "offline"))
  check "LookupFailureShown"
    (((← search? failed "Country").map (·.results)) == some (.failed "offline"))
  let duplicated ← execute searching (.loaded (countries "an") (.ok (Json.mkObj [
    ("found", toJson [germany, germany]),
    ("more", toJson false)])))
  let duplicatedResults ← results? duplicated "Country"
  check "LookupDuplicateResponseFails" (match duplicatedResults with
    | some (.failed _) => true
    | some .loading
    | some (.found ..)
    | none => false)
  let country ← control opened "Country"
  check "LookupTextIsClientBug"
    (match ModelForm.execute (model := Delivery) Delivery.form opened
        (.apply country.key (some (.text "Germany"))) with
    | .error message => message == "Expected a search or a choice."
    | .ok _ => false)
  check "LookupProtocolDecodes"
    (searched (Json.mkObj [("search", "an")]) == some (some "an") &&
      searched (Json.mkObj [("search", Json.null)]) == some none &&
      choiceOf (Json.mkObj [("choose", "\"DE\"")]) == some (some "\"DE\"") &&
      choiceOf (Json.mkObj [("choose", Json.null)]) == some none)

end Tests.Lookup
