module

public import Forms.ExampleForms.Registry
public import Tests.FreshId

public section
namespace Tests.Actions
open Forms.Model Forms.Runtime Tests

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

-- Actions cannot target a read-only input or assign a value of the wrong type.
example : True := by
  let input : InputRef [⟨.readOnly, Nat⟩] Nat := .here
  fail_if_success have bad : Action [⟨.readOnly, Nat⟩] Nat := .set input (.const 1)
  let count : Var [⟨.writable, Nat⟩] Nat := .here
  fail_if_success have bad : Action [⟨.writable, Nat⟩] Nat := .set count (.const true)
  trivial

private def key
  {Γ : Context}
  {α : Type}
  {form : Component Γ α}
  (state : ModelForm.State form)
  (label : String)
  (nth : Nat := 0)
  : IO ControlKey := do
  let controls := (ModelView.render form state.value state.fetchState [] state.env state.locals).controls
  let some found := (controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"FAIL missing button {label} {nth}")
  return found.key

private def press
  {Γ : Context}
  {model : Type}
  [FormModel model]
  [Validation model]
  [Reports model]
  [Lean.ToJson (Raw model)]
  {form : Component Γ (Raw model)}
  (state : ModelForm.State form)
  (label : String)
  (nth : Nat := 0)
  : IO (ModelForm.State form) := do
  IO.ofExcept (ModelForm.execute (model := model) form state (.apply (← key state label nth) none))

private def counter : Component [⟨.readOnly, Nat⟩] Nat := .bind (0 : Nat) (.group "Counter" [
  .field .self "Model" .natural,
  .button "Increment" (.set .here {
    inputs := inputs[.ui (Ref.here), .ui (Ref.there Ref.here), path[]]
    run := fun count step value => count + step + value }),
  .button "Clear" (.set .here (.const 0)),
  .computed "Count" { inputs := inputs[.ui (Ref.here)], run := toString }])

private def next : Component [] Nat := .bind (0 : Nat) (.button "Increment" (.set .here {
  inputs := inputs[.ui (Ref.here)]
  run := fun count => count + 1 }))

private def clicks : Component [] Nat := .bind (0 : Nat) (.button
  { inputs := inputs[.ui (Ref.here)], run := fun count => s!"Clicked {count}" }
  (.set .here { inputs := inputs[.ui (Ref.here)], run := fun count => count + 1 }))

def run : IO Unit := do
  let opened := ModelForm.openState (model := Nat) (supply := supply) counter 10 env[2]
  let increment ← key opened "Increment"
  let clear ← key opened "Clear"
  check "ActionButtonsShareVariableWithoutDeduplication" (increment != clear)
  let once ← press (model := Nat) opened "Increment"
  let twice ← press (model := Nat) once "Increment"
  check "ActionsReadCurrentModelStateAndInputs"
    (twice.locals.value == 24 && twice.value == 10 && twice.env.value == 2)
  let edited ← IO.ofExcept (ModelForm.execute (model := Nat) counter twice
    (.apply (← key twice "Model") (some (.text "3"))))
  let latest ← press (model := Nat) edited "Increment"
  check "ActionsUseLatestModel" (latest.locals.value == 29 && latest.value == 3)
  let cleared ← press (model := Nat) latest "Clear"
  check "ActionConstants" (cleared.locals.value == 0 && cleared.value == latest.value)
  let reset ← IO.ofExcept (ModelForm.execute (model := Nat) counter latest .reset)
  check "ActionResetRestoresLocalState" (reset.locals.value == 0 && reset.value == 10)
  check "ActionRejectsUnexpectedArgument"
    (!(ModelForm.execute (model := Nat) counter opened
      (.apply increment (some (.text "100")))).toBool)
  let disabled := Component.disabledWhen (.const true) counter
  let disabledOpened := ModelForm.openState (model := Nat) (supply := supply) disabled 10 env[2]
  let rejected ← press (model := Nat) disabledOpened "Increment"
  check "ActionDisabledRejects"
    (rejected.ui.rejection == some (toString InvocationError.disabled) && rejected.locals.value == 0)
  let hidden := Component.visibleWhen (.const false) counter
  let hiddenOpened := ModelForm.openState (model := Nat) (supply := supply) hidden 10 env[2]
  let absent ← IO.ofExcept (ModelForm.execute (model := Nat) hidden hiddenOpened (.apply increment none))
  check "ActionHiddenRejects"
    (absent.ui.rejection == some (toString InvocationError.absent) && absent.locals.value == 0)
  let pending : ModelForm.State counter := { opened with ui := { opened.ui with pending := true } }
  let blocked ← press (model := Nat) pending "Increment"
  check "ActionPendingRejects"
    (blocked.ui.rejection == some "Submission is in progress." && blocked.locals.value == 0)
  let nested : Component [] Nat := .bind (0 : Nat) (.bind false
    (.button "Set outer" (.set (.there .here) (.const 7))))
  let nestedUpdated ← press (model := Nat)
    (ModelForm.openState (model := Nat) (supply := supply) nested 10 Env.nil) "Set outer"
  check "ActionCanUpdateOuterBinding"
    (nestedUpdated.locals.value == 7 && nestedUpdated.locals.tail.producer.value == false && nestedUpdated.value == 10)
  let siblings := Component.group "Counters" [next, next]
  let siblingUpdated ← press (model := Nat)
    (ModelForm.openState (model := Nat) (supply := supply) siblings 10 Env.nil) "Increment" 1
  check "ActionSiblingBindingsAreIndependent"
    (siblingUpdated.locals.producer.value == 0 &&
      siblingUpdated.locals.consumers.producer.value == 1)
  let rows : Component [] (Collection Nat) := Component.void <| Component.list .self "Counters"
      (.numbered "Counter") "Add counter" 0 next
  let rowUpdated ← press (model := Collection Nat)
    (ModelForm.openState (model := Collection Nat) (supply := supply) rows
      (.numbered [10, 20]) Env.nil) "Increment" 1
  let removed ← press (model := Collection Nat) rowUpdated "Remove"
  let states : Std.HashMap Uuid
      (ObservationState (Binding Nat (ObservationState (Option PendingCall) Unit))
        (ObservationState (Option PendingCall) Unit)) :=
    removed.locals.producer.producer
  check "ActionRowStateFollowsRemoval"
    (removed.value.values == [20] && states.size == 1 &&
      states[secondId]?.map (·.producer.value) == some 1)
  let adder : Component [] (Collection Nat) :=
    .button "Add" (.append .self (.const 0))
  let added ← press (model := Collection Nat)
    (ModelForm.openState (model := Collection Nat) (supply := supply) adder .empty Env.nil) "Add"
  let addedTwice ← press (model := Collection Nat) added "Add"
  let firstDrawn := supply.next
  check "AppendFreshDrawsSeededDistinctIds"
    (addedTwice.value.ids == [firstDrawn.id, firstDrawn.supply.next.id] &&
      firstDrawn.id != firstDrawn.supply.next.id)
  let functions : Component [] Nat := .bind (fun n : Nat => n)
    (.button "Use successor" (.set .here (.const (fun n : Nat => n + 1))))
  let functionUpdated ← press (model := Nat)
    (ModelForm.openState (model := Nat) (supply := supply) functions 10 Env.nil) "Use successor"
  check "ActionsSupportValuesWithoutCodecs" (functionUpdated.locals.value 41 == 42)
  let focused : Component [] (Collection Nat) := .bind firstId (Component.void <| .zoom?
    { inputs := inputs[.ui (Ref.here)], run := fun id => some (.item id .self) }
    (.button "Next item" (.set .here (.const secondId))))
  let first := ModelForm.openState (model := Collection Nat) (supply := supply) focused
    (.numbered [10, 20]) Env.nil
  let firstKey ← key first "Next item"
  let second ← press (model := Collection Nat) first "Next item"
  let secondKey ← key second "Next item"
  let stale ← IO.ofExcept
    (ModelForm.execute (model := Collection Nat) focused second (.apply firstKey none))
  check "ActionZoomRejectsStaleLocation"
    (firstKey != secondKey && stale.locals.value == secondId &&
      stale.ui.rejection == some (toString InvocationError.absent))
  check "ActionsUseDraftFlushingButtons" (match
      ((ModelView.render counter opened.value {} [] opened.env opened.locals).view.toReact false) with
    | some (.group group) => group.children.any fun
        | .button button => button.onClick == .press (ControlKeyProtocol.toString increment)
        | _ => false
    | _ => false)
  let clicked := ModelForm.openState (model := Nat) (supply := supply) clicks 0 Env.nil
  let first ← key clicked "Clicked 0"
  let clicked ← press (model := Nat) clicked "Clicked 0"
  check "ActionCaptionsAreComputedWithStableKeys" ((← key clicked "Clicked 1") == first)

end Tests.Actions
