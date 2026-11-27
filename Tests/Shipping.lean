module

public import Forms.ExampleForms.Shipping
public import Forms.Runtime.ModelForm
public import Tests.FreshId

public section
namespace Tests.Shipping
open Lean Forms.Model Forms.Runtime
open Forms.ExampleForms.Shipping

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private def control (state : ModelForm.State form) (label : String) : IO Display.Control := do
  let rendered := ModelView.render form state.value state.fetchState [] state.env state.locals
  let controls := rendered.controls
  let some control := controls.find? (·.label == label)
    | throw (IO.userError s!"FAIL missing {label}")
  return control

private def options : Display.Editor → List Display.SelectableOption
  | .choice _ options => options
  | .field ..
  | .lookup ..
  | .action
  | .tabs .. => []

private def express (state : ModelForm.State form) : IO Display.SelectableOption := do
  let some option := (options (← control state "Speed").input).find? (·.label == "Express")
    | throw (IO.userError "FAIL missing Express")
  return option

private def apply
  (state : ModelForm.State form)
  (label : String)
  (argument : String)
  : IO (ModelForm.State form) := do
  let key := (← control state label).key
  IO.ofExcept (ModelForm.execute (model := Parcel) form state (.apply key (some (.text argument))))

def run : IO Unit := do
  let opened := ModelForm.openState (model := Parcel) form initial Env.nil supply
  check "SelectOptionEnabledWithinLimit" ((← express opened).disabledReason == none)
  let heavy ← apply opened "Weight (g)" "40000"
  let option ← express heavy
  check "SelectOptionDisabledWithReason"
    (option.disabledReason == some "Express takes parcels up to 30 kg.")
  let light ← apply heavy "Weight (g)" "1000"
  let chosen ← apply light "Speed" (← express light).value
  check "SelectAcceptsReenabledOption" (chosen.value.speed matches .express)

end Tests.Shipping
