module

public import Forms.ExampleForms.Outputs
public import Forms.Runtime.ModelForm

public section
namespace Tests.Outputs
open Forms.Model Forms.Runtime Forms.ExampleForms.Outputs

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

example : True := by
  let output : InputRef [⟨.readOnly, Nat⟩] Nat := .here
  fail_if_success have bad : Action [⟨.readOnly, Nat⟩] Nat := .set output (.const 5)
  fail_if_success have owner : Var [⟨.readOnly, Nat⟩] Nat := .there .here
  trivial

private def start
  {α β : Type}
  (component : Component [] α β)
  (value : α)
  : ModelForm.State component :=
  ModelForm.load component (ModelForm.openState component value Env.nil)

private def key
  {α β : Type}
  {component : Component [] α β}
  (state : ModelForm.State component)
  (label : String)
  (nth : Nat := 0)
  : IO ControlKey := do
  let controls := state.evaluation.view.controls
  let some control := (controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"FAIL missing {label} {nth}")
  return control.key

private def press
  {model β : Type}
  [FormModel model]
  [Validation model]
  {component : Component [] (FormModel.Raw model) β}
  (state : ModelForm.State component)
  (label : String)
  (nth : Nat := 0)
  : IO (ModelForm.State component) := do
  IO.ofExcept (ModelForm.execute (model := model) component state (.apply (← key state label nth) none))

mutual
private def outputs (label : String) : Display.View → List String
  | .computed name value => if name == label then [value] else []
  | .stack _ children => outputsAll label children
  | .list _ children _ => outputsAll label children
  | .table _ _ rows footer _ => outputsRows label rows ++ outputs label footer
  | _ => []

private def outputsAll (label : String) : List Display.View → List String
  | [] => []
  | view :: rest => outputs label view ++ outputsAll label rest

private def outputsRows (label : String) : List Display.TableRow → List String
  | [] => []
  | ⟨_, cells, _⟩ :: rest => outputsAll label cells ++ outputsRows label rest
end

private def texts
  {α β : Type}
  {component : Component [] α β}
  (state : ModelForm.State component)
  (label : String)
  : List String :=
  outputs label state.evaluation.view

private def functions : Component [] Nat :=
  .observe
    (Component.bind (fun n : Nat => n)
      (.withOutput (.button "Use successor" (.set .here (.const (fun n : Nat => n + 1))))
        { inputs := inputs[.ui (Ref.here)], run := id }))
    (.computed "Result" {
      inputs := inputs[.ui (Ref.here : InputRef _ (Nat → Nat))]
      run := fun f => toString (f 41) })

private def modelDependent : Component [] Nat :=
  .observe
    (Component.bind (0 : Nat)
      (.withOutput (.button "Increment" (.set .here { inputs := inputs[.ui (Ref.here)], run := fun n => n + 1 }))
        { inputs := inputs[.ui (Ref.here), path[]], run := fun count value => count + value }))
    (.group "Consumers" [
      .field .self "Model" .natural,
      .computed "Observed" { inputs := inputs[.ui (Ref.here : InputRef _ Nat)], run := toString }])

def run : IO Unit := do
  let opened := start single 10
  check "ProducerOutputStartsFromOwnedState" (texts opened "Observer one" == ["0"])
  let incremented ← press (model := Nat) opened "Increment"
  check "IndependentObserversReadOwnedOutput"
    (texts incremented "Observer one" == ["1"] && texts incremented "Observer two" == ["Twice: 2"] && incremented.value == 10)
  let privateChanged ← press (model := Nat) incremented "Change private"
  check "PrivateProducerStateIsNotPartOfOutput"
    (texts privateChanged "Observer one" == ["1"] && texts privateChanged "Private value" == ["101"])
  let remembered ← press (model := Nat) privateChanged "Remember output"
  let latest ← press (model := Nat) remembered "Increment"
  check "OutputIsObservedWithoutAStoredCopy"
    (texts latest "Observer one" == ["2"] && texts latest "Remembered" == ["1"])
  let rememberedAgain ← press (model := Nat) latest "Remember output"
  check "ConsumerActionsReadCurrentOutput" (texts rememberedAgain "Remembered" == ["2"])
  let independent := Component.group "Independent instances" [single.void, single.void]
  let independentUpdated ← press (model := Nat) (start independent 10) "Increment"
  check "OutputReferencesBelongToTheirInstance" (texts independentUpdated "Observer one" == ["1", "0"])
  let reset ← IO.ofExcept (ModelForm.execute (model := Nat) single rememberedAgain .reset)
  check "OutputResetRestoresBothSubtrees"
    (texts reset "Observer one" == ["0"] && texts reset "Private value" == ["100"] && texts reset "Remembered" == ["0"])
  let pending := { latest with ui := { latest.ui with pending := true } }
  let rejected ← IO.ofExcept (ModelForm.execute (model := Nat) single pending (.apply (← key pending "Increment") none))
  check "OutputOwnerRespectsPendingState"
    (texts rejected "Observer one" == ["2"] && rejected.ui.rejection == some "Submission is in progress.")

  let rows := start repeated initial
  let first ← press (model := List Nat) rows "Increment"
  let second ← press (model := List Nat) first "Increment" 1
  let twice ← press (model := List Nat) second "Increment" 1
  check "ListCollectsCurrentRowOutputs" (texts twice "Counts" == ["1, 2"] && texts twice "Sum" == ["3"])
  let removed ← press (model := List Nat) twice "Remove"
  check "RemovingRowRemovesItsOutputAndRetainsOthers" (removed.value == [20] && texts removed "Counts" == ["2"])
  let added ← press (model := List Nat) removed "Add counter"
  check "NewRowStartsWithItsOwnOutput" (texts added "Counts" == ["2, 0"])
  let empty ← press (model := List Nat) (← press (model := List Nat) added "Remove") "Remove"
  check "NoRowsMeansNoCollectedOutputs" (texts empty "Counts" == [""] && texts empty "Sum" == ["0"])
  let resetRows ← IO.ofExcept (ModelForm.execute (model := List Nat) repeated twice .reset)
  check "ResetRestoresCollectedOutputs" (texts resetRows "Counts" == ["0, 0"] && resetRows.value == initial)

  let functionUpdated ← press (model := Nat) (start functions 0) "Use successor"
  check "OutputsNeedNoSerialization" (texts functionUpdated "Result" == ["42"])
  let dependent := start modelDependent 10
  let changedModel ← IO.ofExcept (ModelForm.execute (model := Nat) modelDependent dependent
    (.apply (← key dependent "Model") (some (.text "17"))))
  let changedOwner ← press (model := Nat) changedModel "Increment"
  check "OutputObservesConsumerModelEditsAndOwnerStateTogether"
    (changedOwner.value == 17 && texts changedOwner "Observed" == ["18"])

  let pairs := start nested initial
  let left ← press (model := List Nat) pairs "Increment"
  let both ← press (model := List Nat) left "Increment" 1
  let other ← press (model := List Nat) both "Increment" 3
  let otherTwice ← press (model := List Nat) other "Increment" 3
  check "CompositeConsumesChildOutputsAndExportsSum"
    (texts otherTwice "Pair sum" == ["2", "2"] && texts otherTwice "Pair totals" == ["2, 2"] &&
      texts otherTwice "Overall sum" == ["4"])
  let survivor ← press (model := List Nat) otherTwice "Remove"
  check "RepeatedCompositeRetainsNestedStateAfterRemoval"
    (texts survivor "Pair sum" == ["2"] && texts survivor "Overall sum" == ["2"] && survivor.value == [20])

  let loaded : Component [] Nat := .load (.const (.pure true)) fun
    | .ready true => single.void
    | _ => .computed "Status" (.const "Loading")
  let embedded := Component.group "Normal nesting" [loaded, (Component.focus (.const .self) single).void]
  let embeddedUpdated ← press (model := Nat) (start embedded 10) "Increment" 1
  check "ObservationsEmbedUnderLoadAndFocus" (texts embeddedUpdated "Observer one" == ["0", "1"])
  let disabled := Component.disabledWhen (.const true) single
  let disabledOpened := start disabled 10
  let disabledResult ← press (model := Nat) disabledOpened "Increment"
  check "ObservationUsesNormalAvailabilityChecks"
    (disabledResult.ui.rejection == some (toString InvocationError.disabled) && texts disabledResult "Observer one" == ["0"])

  let table : Component [] (List Nat) := Component.void <| .table .self "Rows" "Row" 0 columns[
    "Counters" => .observe pair
      (.computed "Cell total" { inputs := inputs[.ui (Ref.here : InputRef _ Nat)], run := toString })]
  let tableChanged ← press (model := List Nat) (start table initial) "Increment" 1
  check "NestedOutputsWorkInsideTableCells" (texts tableChanged "Cell total" == ["1", "0"])

  let remote : Component [] Nat := .observe counter
    (.loadWith {
      inputs := inputs[.ui (Ref.here : InputRef _ Nat)]
      run := fun count => .fetch { method := .get, url := s!"/count/{count}", body := none } (Lean.fromJson? (α := Nat)) }
      (fun value => .computed "Loaded output" (.const (toString value))))
  let remoteOpened := start remote 10
  check "ConsumerRequestsReadInitialOutput"
    (remoteOpened.outbox == [.fetch { method := .get, url := "/count/0", body := none }])
  let remoteChanged ← press (model := Nat) remoteOpened "Increment"
  check "ConsumerRequestsReadUpdatedOutput"
    (remoteChanged.outbox == [.fetch { method := .get, url := "/count/1", body := none }])
  let remoteLoaded ← IO.ofExcept (ModelForm.execute (model := Nat) remote remoteChanged
    (.loaded { method := .get, url := "/count/1", body := none } (.ok (Lean.toJson (13 : Nat)))))
  check "ObservedConsumersUseNormalLoadLifecycle" (texts remoteLoaded "Loaded output" == ["13"])

  let outer : Component [] Nat := .bind (0 : Nat) <|
    let count : Var [⟨.writable, Nat⟩] Nat := .here
    let observation : Computation [⟨.writable, Nat⟩] Nat Nat := {
      inputs := inputs[.ui count], run := id }
    .observe (Component.withOutput (.computed "Outer count" (toString <$> observation)) observation)
      (.group "Consumer" [
        .button "Set outer" (.set count.there (.const 5)),
        .computed "Outer observed" { inputs := inputs[.ui (Ref.here : InputRef _ Nat)], run := toString }])
  let outerUpdated ← press (model := Nat) (start outer 0) "Set outer"
  check "ConsumerUpdatesPreserveSurroundingContext"
    (texts outerUpdated "Outer count" == ["5"] && texts outerUpdated "Outer observed" == ["5"])

end Tests.Outputs
