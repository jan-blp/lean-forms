module

public import Forms.ExampleForms.Registry
public import Tests.Fetch
public import Tests.FreshId

public section
namespace Tests.Invalidation
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

endpoints Endpoint where
  | search : String → Nat at "/api/counts"
  | other : Nat at "/api/other"

instance : DecidableEq (Api.signature Endpoint.search).Output := inferInstanceAs (DecidableEq Nat)
instance : DecidableEq (Api.signature Endpoint.other).Output := inferInstanceAs (DecidableEq Nat)

private def first := Api.request Endpoint.search "first"
private def second := Api.request Endpoint.search "second"
private def other := Api.request Endpoint.other ()
private def getFirst : HttpRequest := { first with method := .get }

private def form : Component [] Nat :=
  .group "Refresh" [
    .load (.const (Api.source Endpoint.search "first")) fun _ => .computed "First" "",
    .visibleWhen { inputs := inputs[.self], run := (· == 0) } <|
      .load (.const (Api.source Endpoint.search "second")) fun _ => .computed "Second" "",
    .load (.const (Api.source Endpoint.other ())) fun _ => .computed "Other" "",
    .load (.const (.fetch getFirst (fromJson? (α := Nat)))) fun _ => .computed "GET" "",
    .button "One request" (.invalidate (.const (.request first))),
    .button "Whole endpoint" (.invalidate (.const (Api.scope Endpoint.search))),
    .button "Twice" (
      .invalidate (.const (.request first)) ++ .invalidate (.const (.request first))),
    .button "Hide second" (.write .self (.const 1)),
    .button "Show second" (.write .self (.const 0)),
    .disabledWhen (.const true) <|
      .button "Disabled refresh" (.invalidate (.const (Api.scope Endpoint.search))),
    .button "Refresh and write" (
      .invalidate (.const (.request first)) ++ .write .self (.const 3)),
    .button "Write and refresh" (
      .write .self (.const 2) ++ .invalidate {
        inputs := inputs[.self]
        run := fun value => if value == 2 then .request first else .request other })]

private abbrev State := ModelForm.State form

private def execute (state : State) (event : ModelForm.Event Nat) : IO State :=
  IO.ofExcept (ModelForm.execute (model := Nat) form state event)

private def press (state : State) (label : String) : IO State := do
  let some control := state.evaluation.view.controls.find? (·.label == label)
    | throw (IO.userError s!"FAIL missing button {label}")
  execute state (.apply control.key none)

private def fetches (state : State) : List HttpFetch :=
  state.outbox.filterMap fun
    | .fetch fetch => some fetch
    | .submit => none
    | .focus _ => none

private def ready (state : State) (request : HttpRequest) (expected : Nat) : Bool :=
  match state.cache[request]? with
  | some (.loaded json) => (fromJson? (α := Nat) json).toOption == some expected
  | none
  | some (.loading _)
  | some (.failed _) => false

private def opened : State :=
  ModelForm.load form (ModelForm.openState (model := Nat) form 0 Env.nil supply)

private def settled : IO State :=
  (fetches opened).foldlM (init := opened) fun state fetch =>
    execute state (.loaded fetch (.ok (toJson (1 : Nat))))

private def lookupRefresh : IO Unit := do
  let form := BusinessPartners.form
  let execute state event :=
    IO.ofExcept (ModelForm.execute (model := BusinessPartnerSelection) form state event)
  let initial := ModelForm.openState (model := BusinessPartnerSelection)
    form BusinessPartners.initial Env.nil supply
  let some lookup := initial.evaluation.view.controls.find? (·.label == "Business partner")
    | throw (IO.userError "FAIL missing lookup")
  let some refresh := initial.evaluation.view.controls.find? (·.label == "Refresh partners")
    | throw (IO.userError "FAIL missing refresh")
  let searching ← execute initial (.apply lookup.key (some (.lookup (.search ""))))
  let request := Api.request BusinessPartnersEndpoint.search ""
  let original ← IO.ofExcept
    ((LookupResults.select BusinessPartners.candidates (fun _ => True) 5).mapError toString)
  let found ← execute searching
    (.loaded (← pendingFetch searching request) (.ok (toJson original)))
  let key := Reference.wireKey { id := "barcelona", displayText := "" }
  let chosen ← execute found (.apply lookup.key (some (.lookup (.choose key))))
  let reopened ← execute chosen (.apply lookup.key (some (.lookup (.search ""))))
  let refreshing ← execute reopened (.apply refresh.key none)
  let pending ← pendingFetch refreshing request
  check "InvalidationPreservesSelection" (refreshing.value.partner == chosen.value.partner)
  let early ← execute refreshing (.apply lookup.key (some (.lookup (.choose key))))
  check "InvalidationPreventsChoosingStaleResults" early.ui.rejection.isSome
  let changed := BusinessPartners.candidates.map fun candidate =>
    if candidate.reference.id == "barcelona" then
      { candidate with details := { candidate.details with status := .blocked "Newly blocked." } }
    else candidate
  let changed ← IO.ofExcept ((LookupResults.ofList changed false).mapError toString)
  let reloaded ← execute refreshing (.loaded pending (.ok (toJson changed)))
  let rejected ← execute reloaded (.apply lookup.key (some (.lookup (.choose key))))
  check "InvalidationUsesUpdatedAvailability"
    (rejected.ui.rejection ==
      some (toString (InvocationError.disabledMatch key "Newly blocked.")) &&
      rejected.value.partner == chosen.value.partner)

def run : IO Unit := do
  let loaded ← settled
  let one ← press loaded "One request"
  check "InvalidationTargetsOneRequest"
    ((fetches one).map (·.request) == [first] && ready one second 1 && ready one other 1)
  let both ← press loaded "Whole endpoint"
  let requests := (fetches both).map (·.request)
  check "InvalidationTargetsWholeEndpoint"
    (requests.length == 2 && requests.contains first && requests.contains second &&
      ready both other 1 && ready both getFirst 1)
  let twice ← press loaded "Twice"
  check "InvalidationDeduplicatesFetches" ((fetches twice).length == 1)
  let hidden ← press loaded "Hide second"
  let hidden ← press hidden "Whole endpoint"
  check "InvalidationDoesNotFetchInactiveSources"
    ((fetches hidden).map (·.request) == [first] && !hidden.cache.contains second)
  let shown ← press hidden "Show second"
  check "InvalidationFetchesWhenSourceReturns" ((fetches shown).map (·.request) == [second])
  let composed ← press loaded "Write and refresh"
  check "InvalidationComposesWithWrites"
    (composed.value == 2 && (fetches composed).map (·.request) == [first])
  let composed ← press loaded "Refresh and write"
  check "InvalidationSurvivesFollowingSteps"
    (composed.value == 3 && (fetches composed).map (·.request) == [first])
  let disabled ← press loaded "Disabled refresh"
  check "InvalidationRespectsDisabledActions"
    (disabled.ui.rejection.isSome && (fetches disabled).isEmpty && ready disabled first 1)

  let old ← pendingFetch opened first
  let oldSecond ← pendingFetch opened second
  let hidden ← press opened "Hide second"
  let hidden ← press hidden "Whole endpoint"
  let late ← execute hidden (.loaded oldSecond (.ok (toJson (99 : Nat))))
  check "InvalidationIgnoresInactiveResponse" (!late.cache.contains second)
  let refreshing ← press opened "One request"
  let fresh ← pendingFetch refreshing first
  check "InvalidationChangesFetchIdentity" (old != fresh)
  let late ← execute refreshing (.loaded old (.ok (toJson (99 : Nat))))
  check "InvalidationIgnoresLateSuccess" ((← pendingFetch late first) == fresh)
  let late ← execute late (.loaded old (.error "Old failure"))
  check "InvalidationIgnoresLateFailure" ((← pendingFetch late first) == fresh)
  let reloaded ← execute late (.loaded fresh (.ok (toJson (2 : Nat))))
  let late ← execute reloaded (.loaded old (.ok (toJson (99 : Nat))))
  check "InvalidationKeepsNewResponse" (ready late first 2)
  let reset ← execute refreshing .reset
  let again ← press reset "One request"
  check "InvalidationDoesNotReuseIdentityAfterReset"
    ((← pendingFetch again first) != fresh)
  let seeded := ModelForm.load form (ModelForm.openState (model := Nat) form 0 Env.nil supply
    (({} : HttpRequest.Cache).insert first (.loading 12)))
  let refreshed ← press seeded "One request"
  check "InvalidationDoesNotReuseSeededIdentity"
    ((← pendingFetch refreshed first).generation > 12)

  let failed ← execute opened (.loaded old (.error "offline"))
  let retry ← press failed "One request"
  check "InvalidationRetriesFailedSources" ((fetches retry).map (·.request) == [first])
  let fetched ← IO.ofExcept (fetchedRequest ((toJson fresh).compress))
  let fromWire ← IO.ofExcept (ModelForm.Event.fromWire (α := Nat)
    (.fetched (toJson fetched).compress (.response 200 "3")))
  let wire ← execute refreshing fromWire
  check "InvalidationResponseIdentitySurvivesWire" (ready wire first 3)
  lookupRefresh

end Tests.Invalidation
