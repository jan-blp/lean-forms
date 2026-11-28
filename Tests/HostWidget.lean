module

public import Forms.ExampleForms.Swatches
public import Forms.Runtime.ModelProtocol
public import Tests.FreshId

public section
namespace Tests.HostWidget
open Lean Forms.Model Forms.Runtime
open Forms.ExampleForms.Swatches

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private abbrev State := ModelForm.State form

private def control (state : State) (label : String) : IO Display.Control := do
  let some control := (ModelForm.snapshot form state).controls.find? (·.label == label)
    | throw (IO.userError s!"FAIL missing {label}")
  return control

private def send (state : State) (label : String) (argument : Input) : Except String State := do
  let some control := (ModelForm.snapshot form state).controls.find? (·.label == label)
    | throw s!"missing {label}"
  ModelForm.execute (model := Theme) form state (.apply control.key (some argument))

private def pick (state : State) (output : Json) : IO State :=
  IO.ofExcept (send state "Accent" (.hostWidget output))

private def offered (state : State) : IO (List String) := do
  match (← control state "Accent").input with
  | .hostWidget "swatchPicker" input =>
    IO.ofExcept (input.getObjValAs? (List Json) "swatches" >>= (·.mapM (·.getObjValAs? String "id")))
  | .hostWidget ..
  | .field ..
  | .choice ..
  | .lookup ..
  | .action
  | .tabs .. => throw (IO.userError "FAIL Accent is no swatch picker")

private def submitted (state : State) : Bool :=
  (ModelForm.execute (model := Theme) form state .submit).toOption.any fun state =>
    state.outbox.any fun effect => effect == .submit

def run : IO Unit := do
  let opened := ModelForm.openState (model := Theme) form initial Env.nil supply
  check "HostWidgetSeesComputedInput" ((← offered opened) == ["blue", "green", "orange", "purple"])
  let dark ← IO.ofExcept (send opened "Dark background" (.boolean true))
  check "HostWidgetInputFollowsModel" ((← offered dark) == ["blue", "green", "purple"])
  let chosen ← pick opened (Json.mkObj [("id", "orange")])
  check "HostWidgetWritesAcceptedOutput" (chosen.value.accent.val == "orange")
  let refused ← pick dark (Json.mkObj [("id", "orange")])
  check "HostWidgetRefusesUnofferedOutput"
    (refused.value.accent.val == "blue" && refused.ui.rejection.isSome &&
      (← control refused "Accent").errors == ["\"orange\" is not one of the offered colours."])
  check "HostWidgetRefusalBlocksSubmit" (submitted opened && !submitted refused)
  let repicked ← pick refused (Json.mkObj [("id", "green")])
  check "HostWidgetWriteClearsRefusal"
    (repicked.value.accent.val == "green" && (← control repicked "Accent").errors.isEmpty &&
      submitted repicked)
  check "HostWidgetUndecodableOutputIsClientBug" (send opened "Accent" (.hostWidget (toJson 3))).toBool.not
  check "HostWidgetRejectsOtherInput" (send opened "Accent" (.text "green")).toBool.not
  let wire := (ModelForm.snapshot form opened).toWire "swatches" "test" "/api/submit"
  check "HostWidgetListedInSnapshot" (wire.hostWidgets == ["swatchPicker"])
  check "HostWidgetOutputProtocolDecodes"
    (match InputProtocol.fromJson (Json.mkObj [("hostWidget", Json.mkObj [("id", "green")])]) with
    | .ok (.hostWidget output) => output == Json.mkObj [("id", "green")]
    | .ok (.text _)
    | .ok (.boolean _)
    | .ok (.texts _)
    | .ok (.pick _)
    | .ok (.lookup _)
    | .error _ => false)

end Tests.HostWidget
