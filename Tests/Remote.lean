module

public import Forms.ExampleForms.Registry
meta import Forms.Model.Derive
meta import Forms.Deriving.FinEnum

public section
namespace Tests.Remote
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

structure SupplierDetails where
  requiresPurchaseOrder : Bool
  deriving ToJson, FromJson, DecidableEq

/-- The tests' data endpoints. -/
inductive SupplierEndpoint where
  /-- All supplier ids. -/
  | suppliers
  /-- One supplier's details, by id. -/
  | supplier
  deriving DecidableEq, FinEnum, Repr

@[expose] def SupplierEndpoint.signature : SupplierEndpoint → Api.Signature
  | .suppliers => { Input := Unit, Output := List String }
  | .supplier => { Input := String, Output := SupplierDetails }

instance : Api SupplierEndpoint where
  signature := SupplierEndpoint.signature
  path
    | .suppliers => "/api/suppliers"
    | .supplier => "/api/supplier"
  distinct := by decide

def supplierDetails : String → Option SupplierDetails
  | "acme" => some ⟨true⟩
  | "globex" => some ⟨false⟩
  | _ => none

@[expose] def SupplierEndpoint.fixture
  : (named : SupplierEndpoint) → named.signature.Input → Option named.signature.Output
  | .suppliers, _ => some ["acme", "globex"]
  | .supplier, id => supplierDetails id

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

/-- A supplier id; its loaded details decide whether a purchase order is asked for. -/
structure Lookup where
  supplier : String
  purchaseOrder : String
  deriving FormModel

private def Lookup.initial : Lookup.Raw := ⟨"acme", ""⟩

instance : DecidableEq (Api.signature SupplierEndpoint.supplier).Output :=
  inferInstanceAs (DecidableEq SupplierDetails)

private def Lookup.form : Component [] Lookup.Raw :=
  .group (label := "Lookup") (children := [
    .field (path := path[Lookup.Field.supplier]) (label := "Supplier") (editor := .text),
    .loadWith
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

private abbrev State := ModelForm.State Lookup.form

private def execute (state : State) (input : ModelForm.Event) : IO State :=
  IO.ofExcept (ModelForm.execute (model := Lookup) Lookup.form state input)

private def snapshot (state : State) : ModelForm.Snapshot Lookup.Raw :=
  ModelForm.snapshot (model := Lookup) Lookup.form state

private def control? (state : State) (label : String) : Option Display.Control :=
  (snapshot state).controls.find? (·.label == label)

private def apply (state : State) (label : String) (argument : Input) : IO State := do
  let some control := control? state label | throw (IO.userError s!"FAIL no control {label}")
  execute state (.apply control.key (some argument))

private def fetches (state : State) : List HttpRequest :=
  state.outbox.filterMap fun
    | .fetch request => some request
    | .submit => none

private def answer (request : HttpRequest) : Except String Json :=
  (Api.serve SupplierEndpoint.fixture request).elim (.error "Not found.") .ok

/-- Answers every queued request, and the requests their responses queue. -/
private def settle (state : State) : IO State := do
  let mut state := state
  let mut pending := fetches state
  for _ in [0:10] do
    let mut queued := []
    for request in pending do
      state ← execute state (.loaded request (answer request))
      queued := queued ++ fetches state
    pending := queued
  return state

private def supplier (id : String) : HttpRequest := Api.request SupplierEndpoint.supplier id

private def suppliers : HttpRequest := Api.request SupplierEndpoint.suppliers ()

private def layoutRequest : HttpRequest := { method := .post, url := "/api/layout", body := none }

private def nameField : Component [] Person.Raw :=
  .field (path := path[Person.Field.name]) (label := "Name") (editor := .text)

private def ageField : Component [] Person.Raw :=
  .field (path := path[Person.Field.age]) (label := "Age") (editor := .natural)

/-- Name and age in the loaded order; only the name while loading. -/
private def ordered (layout : Source (List String)) : Component [] Person.Raw :=
  .loadOr
    (source := .const layout)
    (fallback := .group (label := "") (children := [nameField]))
    (body := fun order => .group (label := "") (children := order.filterMap fun
      | "name" => some nameField
      | "age" => some ageField
      | _ => none))

/-- Loading can remove options while preserving the choice's location and key. -/
private def shippingChoices : Component [] Order.Raw :=
  let pickup : Branch [] Shipping.Raw :=
    .of Shipping.Constructor.pickup "Pickup" ⟨⟩ (.computed "" (.const ""))
  let standard : Branch [] Shipping.Raw :=
    .of Shipping.Constructor.standard "Standard" ⟨⟨"", ""⟩⟩ (.computed "" (.const ""))
  .load (.const (.fetch layoutRequest (fromJson? (α := Bool)))) fun status =>
    .choice path[Order.Field.shipping] "Shipping" (match status with
      | .ready _ => [standard]
      | _ => [pickup, standard])

private def labels
  {α : Type}
  (form : Component [] α)
  (value : α)
  (cache : HttpRequest.Cache)
  : List String :=
  (ModelView.render form value cache [] Env.nil).controls.map (·.label)

private def performIn
  {α : Type}
  (form : Component [] α)
  (cache : HttpRequest.Cache)
  (value : α)
  (key : ControlKey)
  (argument : Option Input)
  : Except ModelForm.Rejection α := do
  let invocation ← (ModelView.decodeKey form cache value key argument Env.nil).mapError .ofAction
  return invocation.value

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
  let purchaseOrder := ControlKey.edit [.field "purchaseOrder"]
  let early ← execute opened (.apply purchaseOrder (some (.text "PO-1")))
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
  let failed ← execute opened (.loaded (supplier "acme") (.error "offline"))
  check "RemoteFailureShown" (match (snapshot failed).view with
    | .stack _ [_, failure] => failure == .computed "" "Could not load: offline"
    | _ => false)
  let retried ← execute failed .reset
  check "RemoteResetRetries" (fetches retried == [supplier "acme"])
  let person : Person.Raw := ⟨"Ada", 20, true, ⟨"Lambda Lane"⟩⟩
  check "RemoteBindBuildsFromData"
    (labels (ordered (.pure ["age", "name"])) person {} == ["Age", "Name"])
  let pending := ordered (.fetch layoutRequest fromJson?)
  let loadedLayout : HttpRequest.Cache := ({} : HttpRequest.Cache).insert layoutRequest
    (.loaded (toJson ["age", "name"]))
  check "RemoteFallbackWhileLoading" (labels pending person {} == ["Name"])
  let some fallbackName := (ModelView.render pending person {} [] Env.nil).controls.find? (·.label == "Name")
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
  let shippingState := ModelForm.load shippingChoices (ModelForm.openState shippingChoices Order.initial Env.nil)
  let some shipping := (ModelView.render shippingChoices shippingState.value shippingState.cache [] Env.nil).controls.head?
    | throw (IO.userError "FAIL no shipping choice")
  check "RemoteFallbackOffersPickup" (match shipping.input with
    | .choice _ options => options.any (·.value == "pickup")
    | _ => false)
  let shippingState ← IO.ofExcept (ModelForm.execute (model := Order) shippingChoices shippingState
    (.loaded layoutRequest (.ok (toJson true))))
  check "RemoteLoadedChoiceKeepsKey"
    ((ModelView.render shippingChoices shippingState.value shippingState.cache [] Env.nil).controls.any fun control =>
      control.key == shipping.key && match control.input with
        | .choice _ options => options.map (·.value) == ["standard"]
        | _ => false)
  let rejected ← IO.ofExcept (ModelForm.execute (model := Order) shippingChoices shippingState
    (.apply shipping.key (some (.text "pickup"))))
  check "RemoteRemovedBranchRejectsRecoverably"
    (rejected.ui.rejection == some (toString (InvocationError.unavailableBranch "pickup")) &&
      toJson rejected.value == toJson shippingState.value)
  let recovered ← IO.ofExcept (ModelForm.execute (model := Order) shippingChoices rejected
    (.apply shipping.key (some (.text "standard"))))
  check "RemoteChoiceUsableAfterStaleBranch" recovered.ui.rejection.isNone
  let twice : Component [] Person.Raw := .group (label := "") (children := [nameField, nameField])
  let rendered := ModelView.render twice person {} [] Env.nil
  check "RemoteDuplicateShownOnce"
    (rendered.controls.map (·.label) == ["Name"] && match rendered.view with
      | .stack _ [.control _, .computed "Name" note] => note == Display.duplicateNote
      | _ => false)
  let late ← execute loaded (.loaded (supplier "initech") (.ok Json.null))
  check "RemoteUnrequestedResponseIgnored" !(late.cache.contains (supplier "initech"))

end Tests.Remote
