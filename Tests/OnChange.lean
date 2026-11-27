module

public import Forms.ExampleForms.ExchangeRate
public import Forms.Runtime.FormDefinition
public import Forms.Runtime.ModelForm
public import Tests.FreshId
public import Tests.Fetch
meta import Forms.Model.Derive

public section
namespace Tests.OnChange
open Lean Forms.Model Forms.Model.Sugar Forms.Runtime
open Forms.ExampleForms.ExchangeRate

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private abbrev State := ModelForm.State form

private def execute (state : State) (input : ModelForm.Event Transfer.Raw) : IO State :=
  IO.ofExcept (ModelForm.execute (model := Transfer) form state input)

private def control (state : State) (label : String) : IO Display.Control := do
  let some control := (ModelForm.snapshot form state).controls.find? (·.label == label)
    | throw (IO.userError s!"FAIL no control {label}")
  return control

private def apply (state : State) (label : String) (argument : Input) : IO State := do
  execute state (.apply (← control state label).key (some argument))

private def choose (state : State) (option : String) : IO State := do
  let options := match (← control state "Currency").input with
    | .choice _ options => options
    | .field ..
    | .lookup ..
    | .action
    | .tabs .. => []
  let some chosen := options.find? (·.label == option)
    | throw (IO.userError s!"FAIL no option {option}")
  apply state "Currency" (.text chosen.value)

private def settle (state : State) : IO State :=
  state.outbox.foldlM (init := state) fun state effect => match effect with
    | .fetch fetch => do
      execute state (.loaded (← pendingFetch state fetch.request)
        ((serve fetch.request).elim (.error "Not found.") .ok))
    | .submit
    | .focus _ => pure state

structure Order where
  quantity : Nat
  copied : Nat
  done : Bool
  deriving FormModel

def fresh : Component [] Order.Raw := named%
  observe% doubled := .output { inputs := inputs[path[Order.Field.quantity]], run := (· * 2) };
  .onChange (fun _ _ => .write path[Order.Field.copied] { inputs := inputs[ref[doubled]], run := id })
    (.field path[Order.Field.quantity] "Quantity" .natural)

def nested : Component [] Order.Raw :=
  .onChange (fun old new => .write path[Order.Field.copied] (.const (new.copied - old.copied + 100))) <|
    .onChange (fun _ new => .write path[Order.Field.copied] (.const new.quantity))
      (.field path[Order.Field.quantity] "Quantity" .natural)

def hidden : Component [] Order.Raw :=
  .visibleWhen { inputs := inputs[path[Order.Field.done]], run := not } <|
    .onChange (fun _ _ => .write path[Order.Field.copied] (.const 99)) <|
      .group "Order" [
        .field path[Order.Field.quantity] "Quantity" .natural,
        .field path[Order.Field.done] "Done" .checkbox]

def zoomed : Component [] Order.Raw :=
  .group "Order" [
    Component.void <| .zoom?
      { inputs := inputs[path[Order.Field.quantity]]
        run := fun quantity => if quantity == 0 then none else some (.ofPath path[Order.Field.quantity]) }
      (.onChange (fun _ _ => .write path[] (.const 77)) (.field .self "Quantity" .natural)),
    .button "Restore" (.write path[Order.Field.quantity] (.const 3))]

def retargeted : Component [] Order.Raw :=
  Component.void <| .zoom?
    { inputs := inputs[path[Order.Field.quantity]]
      run := fun quantity => some (if quantity == 1 then .ofPath path[Order.Field.quantity]
        else .ofPath path[Order.Field.copied]) }
    (.onChange (fun old new => .write path[] (.const (old + new + 100)))
      (.field .self "Value" .natural))

private def step
  {form : Component [] Order.Raw}
  (state : ModelForm.State form)
  (label : String)
  (argument : Option Input)
  : IO (ModelForm.State form) := do
  let some control := (ModelForm.snapshot form state).controls.find? (·.label == label)
    | throw (IO.userError s!"FAIL no control {label}")
  IO.ofExcept (ModelForm.execute (model := Order) form state (.apply control.key argument))

private def edit
  (form : Component [] Order.Raw)
  (label : String)
  (argument : Input)
  : IO Order.Raw := do
  let opened := ModelForm.openState (model := Order) form ⟨0, 0, false⟩ Env.nil supply
  return (← step opened label (some argument)).value

def run : IO Unit := do
  check "OnChangeReadsFreshOutputs" ((← edit fresh "Quantity" (.text "5")).copied == 10)
  check "OnChangeRunsInnermostFirst" ((← edit nested "Quantity" (.text "5")).copied == 105)
  check "OnChangeRunsWhileShown" ((← edit hidden "Quantity" (.text "5")).copied == 99)
  check "OnChangeDropsHiddenReaction" ((← edit hidden "Done" (.boolean true)).copied == 0)
  let shown := ModelForm.openState (model := Order) zoomed ⟨1, 0, false⟩ Env.nil supply
  let gone ← step shown "Quantity" (some (.text "0"))
  let restored ← step gone "Restore" none
  check "OnChangeDropsReactionOfMissingTarget"
    (gone.value.quantity == 0 && restored.value.quantity == 3)
  let moved ← step (ModelForm.openState (model := Order) retargeted ⟨1, 10, false⟩ Env.nil supply)
    "Value" (some (.text "2"))
  check "OnChangeDropsReactionOfMovedTarget" (moved.value.quantity == 2 && moved.value.copied == 10)
  let definition := FormDefinition.ofModel Transfer form initial
  let (opened, _) ← IO.ofExcept (definition.openState (toJson initial) supply)
  let opened : State := opened
  let early ← choose opened "USD"
  check "OnChangeKeepsRateWhileLoading"
    (early.value.currency == .usd && early.value.rate == ⟨1, 0, by decide⟩)
  let loaded ← settle opened
  let swiss ← choose loaded "CHF"
  check "OnChangeWritesLoadedRate"
    (swiss.value.currency == .chf && swiss.value.rate == ⟨107, 2, by decide⟩)
  let edited ← apply swiss "Rate to EUR" (.text "1.1")
  let amount ← apply edited "Amount" (.text "250")
  check "OnChangeIgnoresEditsOutsideBody" (amount.value.rate == ⟨11, 1, by decide⟩)
  let same ← choose amount "CHF"
  check "OnChangeSameCurrencyKeepsRate" (same.value.rate == ⟨11, 1, by decide⟩)

end Tests.OnChange
