module

public import Forms.ExampleForms.Registry

public section
namespace Tests.Remote
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private abbrev State := ModelForm.State Invoice.Raw

private def execute (state : State) (command : ModelForm.Command) : IO State :=
  IO.ofExcept (ModelForm.execute (model := Invoice) Invoice.form state command)

private def snapshot (state : State) : ModelForm.Snapshot Invoice.Raw :=
  ModelForm.snapshot (model := Invoice) Invoice.form state

private def control? (state : State) (label : String) : Option Display.Control :=
  (snapshot state).controls.find? (·.label == label)

private def options (state : State) (label : String) : List String :=
  match ((control? state label).map (·.input) : Option Display.Editor) with
  | some (.choice _ options) => options.map (·.value)
  | _ => []

private def apply (state : State) (label : String) (argument : Input) : IO State := do
  let some control := control? state label | throw (IO.userError s!"FAIL no control {label}")
  execute state (.event (.apply control.key (some argument)))

private def fetches (state : State) : List HttpRequest :=
  state.outbox.filterMap fun
    | .fetch request => some request
    | .submit => none

private def answer (request : HttpRequest) : Except String Json :=
  (api request).elim (.error "Not found.") .ok

/-- Answers every queued request, and the requests their responses queue. -/
private def settle (state : State) : IO State := do
  let mut state := state
  let mut pending := fetches state
  for _ in [0:10] do
    let mut queued := []
    for request in pending do
      state ← execute state (.event (.loaded request (answer request)))
      queued := queued ++ fetches state
    pending := queued
  return state

private def supplier (id : String) : HttpRequest := Api.request SupplierEndpoint.supplier id

private def suppliers : HttpRequest := Api.request SupplierEndpoint.suppliers ()

/-- Writes the loaded data instead of the value. -/
private def writesData : Component String :=
  .load
    (source := .const (.pure ""))
    (body := .field (path := path[Scope.Field.context]) (label := "Data") (editor := .text))

/-- Writes the picked key instead of its payload. -/
private def writesKey : Component (Selection String Unit) :=
  .keyed
    (path := .self)
    (label := "Key")
    (options := .const [])
    (initial := ())
    (body := .field (path := path[Scope.Field.context]) (label := "Key") (editor := .text))

def run : IO Unit := do
  check "RemoteWellFormed"
    (Invoice.form.wellFormed && !writesData.wellFormed && !writesKey.wellFormed)
  check "RemoteApiRoundtrip" ([suppliers, supplier "acme"].all fun request =>
    ((Api.parse (endpoint := SupplierEndpoint) request).map fun call => Api.request call.named call.input)
      == some request)
  check "RemoteApiRejects" ([{ suppliers with method := .get }, { suppliers with url := "/api/missing" },
    { supplier "acme" with body := some "1" }].all (Api.parse (endpoint := SupplierEndpoint) · |>.isNone))
  check "RemoteUnitUsesCoreCodec" (suppliers.body == some "{}")
  check "RemoteFetchEffectRoundtrip" (match fetchEffect (supplier "acme") with
    | .fetch id _ => (fetchedRequest id).toOption == some (supplier "acme")
    | .submit _ => false)
  let (opened, _) ← IO.ofExcept
    ((FormDefinition.ofModel Invoice Invoice.form Invoice.initial).openState (toJson Invoice.initial))
  let opened : State := opened
  check "RemoteOpenFetchesOptions" (fetches opened == [suppliers])
  check "RemoteOptionsLoading" (control? opened "Supplier").isNone
  let early ← execute opened (.event (.apply (DisplayProtocol.controlKey ⟨[0]⟩) (some (.text "acme"))))
  check "RemoteSelectBeforeLoadRejects"
    ((snapshot early).ui.rejection == some (toString InvocationError.notLoaded))
  let loaded ← settle opened
  check "RemoteOptionsLoaded" (options loaded "Supplier" == ["acme", "globex", "initech"])
  let unknown ← apply loaded "Supplier" (.text "nope")
  check "RemoteUnknownOptionRejects"
    ((snapshot unknown).ui.rejection == some (toString InvocationError.unknownOption))
  let acme ← apply loaded "Supplier" (.text "acme")
  check "RemoteSelectFetchesDetails" (fetches acme == [supplier "acme"])
  check "RemoteDetailsLoading" (control? acme "Contact").isNone
  let acme ← settle acme
  check "RemoteDependentOptions" (options acme "Contact" == ["anna", "ben"])
  let acme ← apply acme "Purchase order" (.text "PO-1")
  let acme ← apply acme "Contact" (.text "ben")
  let globex ← settle (← apply acme "Supplier" (.text "globex"))
  check "RemoteDetailDrivesVisibility"
    ((control? acme "Purchase order").isSome && (control? globex "Purchase order").isNone)
  let back ← apply globex "Supplier" (.text "acme")
  check "RemoteReselectIsCached" (fetches back).isEmpty
  check "RemoteReselectKeepsPayload"
    ((toJson back.value.supplier) == toJson ({ selected := some ("acme",
      ⟨{ selected := some ("ben", ()), stash := {} }, "PO-1"⟩), stash := {} } :
        Selection String SupplierPart.Raw))
  let failed ← execute opened (.event (.loaded suppliers (.error "offline")))
  check "RemoteFailureShown" (match (snapshot failed).view with
    | .stack _ (first :: _) => first == .computed "" "Could not load: offline"
    | _ => false)
  let retried ← execute failed (.event .reset)
  check "RemoteResetRetries" (fetches retried == [suppliers])
  let late ← execute loaded (.event (.loaded (supplier "initech") (.ok Json.null)))
  check "RemoteUnrequestedResponseIgnored" !(late.cache.contains (supplier "initech"))

end Tests.Remote
