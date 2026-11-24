module

public import Forms.ExampleForms.Registry
public import Tests.FreshId
public meta import Forms.Model.Lookup.Theorems

public section
namespace Tests.LookupCandidates
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private def control
  {α β : Type}
  (form : Component [] α β)
  (state : ModelForm.State form)
  (label : String)
  : IO Display.Control := do
  let some control := (ModelForm.snapshot form state).controls.find? (·.label == label)
    | throw (IO.userError s!"FAIL no control {label}")
  return control

private abbrev State := ModelForm.State BusinessPartners.form

private def execute
  (state : State)
  (event : ModelForm.Event BusinessPartnerSelection.Raw)
  : IO State :=
  IO.ofExcept (ModelForm.execute (model := BusinessPartnerSelection) BusinessPartners.form state event)

private def apply (state : State) (command : LookupInput) : IO State := do
  let lookup := (← control BusinessPartners.form state "Business partner").key
  execute state (.apply lookup (some (.lookup command)))

private def key (id : String) : LookupKey :=
  Reference.wireKey { id, displayText := "" }

private def snapshot (state : State) := ModelForm.snapshot BusinessPartners.form state

private def settle (state : State) : IO State :=
  state.outbox.foldlM (init := state) fun state effect => match effect with
    | .fetch request =>
      execute state (.loaded request ((BusinessPartners.serve request).elim (.error "Not found.") .ok))
    | .submit => pure state
    | .focus _ => pure state

structure Restricted where
  partner : Option (Reference String)
  locked : Bool
  deriving FormModel

private def restrictedForm : Component [] Restricted.Raw :=
  .group "Restricted" [
    .field path[Restricted.Field.locked] "Locked" .checkbox,
    .lookup path[Restricted.Field.partner] "Business partner"
      (.const (Api.source BusinessPartnersEndpoint.search))
      { inputs := inputs[path[Restricted.Field.locked]]
        run := fun locked candidate =>
          if locked then .disabled "Selection is locked."
          else BusinessPartners.availability candidate }]

def run : IO Unit := do
  let results ← IO.ofExcept
    ((LookupResults.select BusinessPartners.candidates (fun _ => True) 5).mapError toString)
  let decoded ← IO.ofExcept (fromJson? (α := LookupResults String BusinessPartnerData) (toJson results))
  check "CandidatePayloadRoundtrip" (decoded.found == results.found)
  let some candidate := results.found.head? | throw (IO.userError "FAIL missing candidate")
  let duplicate := { candidate with data := { candidate.data with status := .active } }
  check "CandidateDuplicateIdsIgnorePayload"
    ((LookupResults.select [candidate, duplicate] (fun _ => True) 0).isOk |> not)
  check "CandidateDuplicateJsonRejected"
    ((fromJson? (α := LookupResults String BusinessPartnerData) (Json.mkObj [
      ("found", toJson [candidate, duplicate]), ("more", toJson false)])).isOk |> not)
  let definition :=
    FormDefinition.ofModel BusinessPartnerSelection BusinessPartners.form BusinessPartners.initial
  let (opened, _) ← IO.ofExcept (definition.openState (toJson BusinessPartners.initial) supply)
  let searching ← apply opened (.search "")
  let early ← apply searching (.choose (key "barcelona"))
  check "CandidateChooseBeforeLoadingRejected" ((snapshot early).ui.rejection.isSome)
  let found ← settle searching
  let foundControl ← control BusinessPartners.form found "Business partner"
  let options ← match foundControl.input with
    | .lookup _ (some { results := .found options _, .. }) => pure options
    | .lookup _ none
    | .lookup _ (some { results := .loading, .. })
    | .lookup _ (some { results := .failed _, .. })
    | .field ..
    | .choice ..
    | .action
    | .tabs .. => throw (IO.userError "FAIL missing candidate options")
  check "CandidateDisabledReasonProjected"
    (options.map (·.disabledReason) == [some "Account is blocked.", none, some "Account is closed.", none,
      some "Account is blocked."])
  let wire := (snapshot found).toWire "business-partners" "test" "/api/submit"
  check "CandidatePayloadNotSentToReact" (!(toJson wire.view).compress.contains "VAT-200")
  let rejected ← apply found (.choose (key "alpine"))
  check "CandidateForgedDisabledChoiceRejected"
    ((snapshot rejected).ui.rejection ==
      some (toString (InvocationError.disabledMatch (key "alpine") "Account is blocked.")) &&
      rejected.value.partner.isNone && rejected.locals.isSome)
  let chosen ← apply found (.choose (key "barcelona"))
  check "CandidateChooseStoresOnlyReference"
    (chosen.value.partner == some { id := "barcelona", displayText := "Barcelona Office" } &&
      toJson chosen.value == Json.mkObj [
        ("partner", Json.mkObj [("id", "barcelona"), ("displayText", "Barcelona Office")])])
  let reopened ← settle (← apply chosen (.search ""))
  let rejected ← apply reopened (.choose (key "girona"))
  check "CandidateDisabledChoicePreservesSelection"
    (rejected.value.partner == chosen.value.partner && rejected.locals.isSome)
  let byVat ← settle (← apply chosen (.search "VAT-400"))
  let byVat ← apply byVat (.choose (key "vic"))
  check "CandidateSearchUsesTypedPayload" (byVat.value.partner.map (·.id) == some "vic")
  let closed ← apply reopened .close
  let stale ← apply closed (.choose (key "barcelona"))
  check "CandidateClosedSearchRejectsChoice" ((snapshot stale).ui.rejection.isSome)

  let initial : Restricted.Raw := { partner := none, locked := false }
  let definition := FormDefinition.ofModel Restricted restrictedForm initial
  let (opened, _) ← IO.ofExcept (definition.openState (toJson initial) supply)
  let execute state event :=
    IO.ofExcept (ModelForm.execute (model := Restricted) restrictedForm state event)
  let lookup := (← control restrictedForm opened "Business partner").key
  let searching ← execute opened (.apply lookup (some (.lookup (.search ""))))
  let request := Api.request BusinessPartnersEndpoint.search ""
  let found ← execute searching (.loaded request (.ok (toJson results)))
  let locked ← execute found
    (.apply (← control restrictedForm found "Locked").key (some (.boolean true)))
  let rejected ← execute locked (.apply lookup (some (.lookup (.choose (key "barcelona")))))
  check "CandidateAvailabilityReevaluated"
    ((ModelForm.snapshot restrictedForm rejected).ui.rejection ==
      some (toString (InvocationError.disabledMatch (key "barcelona") "Selection is locked.")) &&
      rejected.value.partner.isNone)

end Tests.LookupCandidates
