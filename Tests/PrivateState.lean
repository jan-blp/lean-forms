module

public import Forms.ExampleForms.PrivateState
public import Forms.Runtime.ModelForm
public import Tests.FreshId
meta import Forms.Model.Derive

public section
namespace Tests.PrivateState
open Lean Forms.Model Forms.Model.Sugar Forms.Runtime
open Forms.ExampleForms.PrivateState

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private def view (state : ModelForm.State form) : Display.View :=
  (ModelView.render form state.value state.fetchState [] state.env state.locals).view

private def control (state : ModelForm.State form) (label : String) : Option Display.Control :=
  (view state).controls.find? (·.label == label)

mutual
private def computed (label : String) : Display.View → List String
  | .computed name value => if name == label then [value] else []
  | .stack _ children => computedAll label children
  | .list (children := children) .. => computedAll label children
  | .table (footer := footer) .. => computed label footer
  | .keyed _ body => computed label body
  | .control _ => []
  | .marker _ => []
  | .hidden => []

private def computedAll (label : String) : List Display.View → List String
  | [] => []
  | view :: rest => computed label view ++ computedAll label rest
end

private def apply
  (state : ModelForm.State form)
  (label : String)
  (argument : Input)
  : IO (ModelForm.State form) := do
  let some control := control state label | throw (IO.userError s!"FAIL missing {label}")
  IO.ofExcept
    (ModelForm.execute (model := Shipment) form state (.apply control.key (some argument)))

private def chosen : Display.Editor → Option String
  | .choice shown _ => some shown
  | .field ..
  | .lookup ..
  | .action
  | .tabs .. => none

private def choiceOptions : Display.Editor → List Display.ChoiceOption
  | .choice _ options => options
  | .field ..
  | .lookup ..
  | .action
  | .tabs .. => []

private def isState : ControlKey → Bool
  | .state .. => true
  | .edit _
  | .select _
  | .press ..
  | .tab .. => false

structure Label where
  recipient : String
  deriving FormModel

def labelForm : Component [] Label.Raw := named%
  state% copies := (1 : Nat);
  .group "Label" [
    .field path[Label.Field.recipient] "Recipient" .text,
    .stateField ref[copies] "Copies" .natural]

private def copies (state : ModelForm.State labelForm) : Option Display.Control :=
  state.evaluation.view.controls.find? (·.label == "Copies")

private def label
  (state : ModelForm.State labelForm)
  (event : ModelForm.Event Label.Raw)
  : IO (ModelForm.State labelForm) :=
  IO.ofExcept (ModelForm.execute (model := Label) labelForm state event)

private def rejectedText : IO Unit := do
  let opened := ModelForm.openState (model := Label) labelForm ⟨"Ada"⟩ Env.nil supply
  let some key := (copies opened).map (·.key) | throw (IO.userError "FAIL missing copies")
  let rejected ← label opened (.apply key (some (.text "-3")))
  let shown (state : ModelForm.State labelForm) :=
    (copies state).any (·.messages.any (·.kind == .error))
  check "PrivateStateRejectedTextShowsOnControl" (shown rejected)
  check "PrivateStateRejectedTextDoesNotBlockSubmit" (← label rejected .submit).ui.pending
  check "PrivateStateDraftClearsRejection" !(shown (← label rejected (.draft key none)))
  let fixed ← label rejected (.apply key (some (.text "2")))
  check "PrivateStateCommitClearsRejection" !(shown fixed)

def run : IO Unit := do
  rejectedText
  let opened := ModelForm.openState (model := Shipment) form initial Env.nil supply
  check "PrivateStateControlsAreKeyedAsState"
    ((control opened "Show advanced options").any (isState ·.key) &&
      (control opened "Show weight in").any (isState ·.key) &&
      (control opened "Recipient").any (!isState ·.key))
  check "PrivateStateHidesAdvancedInitially" (control opened "Delivery instructions").isNone
  let advanced ← apply opened "Show advanced options" (.boolean true)
  check "PrivateStateFieldRevealsAdvanced"
    ((control advanced "Delivery instructions").isSome &&
      (control advanced "Show advanced options").any
        (·.input == .field (.checkbox true) .unsupported))
  let some weightUnit := control advanced "Show weight in"
    | throw (IO.userError "FAIL missing unit")
  let some kilograms := (choiceOptions weightUnit.input).find? (·.label == "Kilograms")
    | throw (IO.userError "FAIL missing kilograms option")
  let converted ← apply advanced "Show weight in" (.text kilograms.value)
  check "PrivateStateSelectChangesView"
    (computed "Weight" (view converted) == ["1.250 kg"] &&
      (control converted "Show weight in").bind (chosen ·.input) == some kilograms.value)
  let renamed ← apply converted "Recipient" (.text "Grace")
  check "PrivateStateSurvivesModelEdits"
    ((control renamed "Delivery instructions").isSome &&
      computed "Weight" (view renamed) == ["1.250 kg"])

end Tests.PrivateState
