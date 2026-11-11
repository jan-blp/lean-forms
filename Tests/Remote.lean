module

public import Forms.ExampleForms.Registry
meta import Forms.Model.Derive

public section
namespace Tests.Remote
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

/-- A supplier id; its loaded details decide whether a purchase order is asked for. -/
structure Lookup where
  supplier : String
  purchaseOrder : String
  deriving FormModel

private def Lookup.initial : Lookup.Raw := ⟨"acme", ""⟩

private def Lookup.form : Component Lookup.Raw :=
  .group (label := "Lookup") (children := [
    .field (path := path[Lookup.Field.supplier]) (label := "Supplier") (editor := .text),
    .bind
      (source := {
        inputs := inputs[path[Lookup.Field.supplier]]
        run := Api.source SupplierEndpoint.supplier
      })
      (body := fun details => .visibleWhen
        (condition := .const details.requiresPurchaseOrder)
        (body := .field
          (path := path[Lookup.Field.purchaseOrder])
          (label := "Purchase order")
          (editor := .text)))])

private abbrev State := ModelForm.State Lookup.Raw

private def execute (state : State) (command : ModelForm.Command) : IO State :=
  IO.ofExcept (ModelForm.execute (model := Lookup) Lookup.form state command)

private def snapshot (state : State) : ModelForm.Snapshot Lookup.Raw :=
  ModelForm.snapshot (model := Lookup) Lookup.form state

private def control? (state : State) (label : String) : Option Display.Control :=
  (snapshot state).controls.find? (·.label == label)

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

private def layoutRequest : HttpRequest := { method := .post, url := "/api/layout", body := none }

private def nameField : Component Person.Raw :=
  .field (path := path[Person.Field.name]) (label := "Name") (editor := .text)

private def ageField : Component Person.Raw :=
  .field (path := path[Person.Field.age]) (label := "Age") (editor := .natural)

/-- Name and age in the loaded order; only the name while loading. -/
private def ordered (layout : Source (List String)) : Component Person.Raw :=
  .bindOr
    (source := .const layout)
    (fallback := .group (label := "") (children := [nameField]))
    (body := fun order => .group (label := "") (children := order.filterMap fun
      | "name" => some nameField
      | "age" => some ageField
      | _ => none))

private def labels
  {raw : Type}
  (form : Component raw)
  (value : raw)
  (cache : HttpRequest.Cache)
  : List String :=
  (ModelView.render form value cache).controls.map (·.label)

private def performIn
  {raw : Type}
  (form : Component raw)
  (cache : HttpRequest.Cache)
  (value : raw)
  (key : ControlKey)
  (argument : Option Input)
  : Except ModelForm.Rejection raw := do
  let invocation ← (ModelView.decodeKey form cache value key argument).mapError .ofAction
  return form.applyValid cache value invocation

def run : IO Unit := do
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
    ((FormDefinition.ofModel Lookup Lookup.form Lookup.initial).openState (toJson Lookup.initial))
  let opened : State := opened
  check "RemoteOpenFetches" (fetches opened == [supplier "acme"])
  check "RemoteDetailsLoading" (control? opened "Purchase order").isNone
  let purchaseOrder := DisplayProtocol.controlKey .edit [.field "purchaseOrder"]
  let early ← execute opened (.event (.apply purchaseOrder (some (.text "PO-1"))))
  check "RemoteEditBeforeLoadRejects"
    ((snapshot early).ui.rejection == some (toString InvocationError.absent))
  let loaded ← settle opened
  check "RemoteDetailsLoaded" (control? loaded "Purchase order").isSome
  let globex ← apply loaded "Supplier" (.text "globex")
  check "RemoteInputRefetches" (fetches globex == [supplier "globex"])
  let globex ← settle globex
  check "RemoteDetailDrivesVisibility" (control? globex "Purchase order").isNone
  let back ← apply globex "Supplier" (.text "acme")
  check "RemoteRevisitIsCached" (fetches back).isEmpty
  let failed ← execute opened (.event (.loaded (supplier "acme") (.error "offline")))
  check "RemoteFailureShown" (match (snapshot failed).view with
    | .stack _ [_, failure] => failure == .computed "" "Could not load: offline"
    | _ => false)
  let retried ← execute failed (.event .reset)
  check "RemoteResetRetries" (fetches retried == [supplier "acme"])
  let person : Person.Raw := ⟨"Ada", 20, true, ⟨"Lambda Lane"⟩⟩
  check "RemoteBindBuildsFromData"
    (labels (ordered (.pure ["age", "name"])) person {} == ["Age", "Name"])
  let pending := ordered (.fetch layoutRequest fromJson?)
  let loadedLayout : HttpRequest.Cache := ({} : HttpRequest.Cache).insert layoutRequest
    (.loaded (toJson ["age", "name"]))
  check "RemoteFallbackWhileLoading" (labels pending person {} == ["Name"])
  let some fallbackName := (ModelView.render pending person {}).controls.find? (·.label == "Name")
    | throw (IO.userError "FAIL no fallback control")
  let fallbackName := fallbackName.key
  check "RemoteFallbackEditable"
    ((performIn pending {} person fallbackName (some (.text "Grace"))).toOption.map (·.name)
      == some "Grace")
  check "RemoteBodyAfterLoad" (labels pending person loadedLayout == ["Age", "Name"])
  let renamed (cache : HttpRequest.Cache) : Option String :=
    (performIn pending cache person fallbackName (some (.text "Grace"))).toOption.map (·.name)
  check "RemoteKeySurvivesLoad" (renamed loadedLayout == some "Grace")
  let otherLayout : HttpRequest.Cache := ({} : HttpRequest.Cache).insert layoutRequest
    (.loaded (toJson ["name", "age"]))
  check "RemoteReorderedKeepsField" (renamed otherLayout == some "Grace")
  let twice : Component Person.Raw := .group (label := "") (children := [nameField, nameField])
  let rendered := ModelView.render twice person {}
  check "RemoteDuplicateShownOnce"
    (rendered.controls.map (·.label) == ["Name"] && match rendered.view with
      | .stack _ [.control _, .computed "Name" note] => note == Display.duplicateNote
      | _ => false)
  let late ← execute loaded (.event (.loaded (supplier "initech") (.ok Json.null)))
  check "RemoteUnrequestedResponseIgnored" !(late.cache.contains (supplier "initech"))

end Tests.Remote
