module

public import Forms.ExampleForms.Registry

public section
namespace Tests.Actions
open Forms.Model Forms.Runtime

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
  let controls := (ModelView.render form state.value state.cache [] state.env state.locals).controls
  let some found := (controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"FAIL missing button {label} {nth}")
  return found.key

private def press
  {Γ : Context}
  {model : Type}
  [FormModel model]
  [Validation model]
  {form : Component Γ (FormModel.Raw model)}
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
  let opened := ModelForm.openState counter 10 env[2]
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
  let disabledOpened := ModelForm.openState disabled 10 env[2]
  let rejected ← press (model := Nat) disabledOpened "Increment"
  check "ActionDisabledRejects"
    (rejected.ui.rejection == some (toString InvocationError.disabled) && rejected.locals.value == 0)
  let hidden := Component.visibleWhen (.const false) counter
  let hiddenOpened := ModelForm.openState hidden 10 env[2]
  let absent ← IO.ofExcept (ModelForm.execute (model := Nat) hidden hiddenOpened (.apply increment none))
  check "ActionHiddenRejects"
    (absent.ui.rejection == some (toString InvocationError.absent) && absent.locals.value == 0)
  let pending : ModelForm.State counter := { opened with ui := { opened.ui with pending := true } }
  let blocked ← press (model := Nat) pending "Increment"
  check "ActionPendingRejects"
    (blocked.ui.rejection == some "Submission is in progress." && blocked.locals.value == 0)
  let nested : Component [] Nat := .bind (0 : Nat) (.bind false
    (.button "Set outer" (.set (.there .here) (.const 7))))
  let nestedUpdated ← press (model := Nat) (ModelForm.openState nested 10 Env.nil) "Set outer"
  check "ActionCanUpdateOuterBinding"
    (nestedUpdated.locals.value == 7 && nestedUpdated.locals.tail.value == false && nestedUpdated.value == 10)
  let siblings := Component.group "Counters" [next, next]
  let siblingUpdated ← press (model := Nat) (ModelForm.openState siblings 10 Env.nil) "Increment" 1
  check "ActionSiblingBindingsAreIndependent"
    (siblingUpdated.locals.producer.value == 0 &&
      siblingUpdated.locals.consumers.producer.value == 1)
  let rows : Component [] (List Nat) := Component.void <| Component.list .self "Counters" "Counter" 0 next
  let rowUpdated ← press (model := List Nat) (ModelForm.openState rows [10, 20] Env.nil) "Increment" 1
  let removed ← press (model := List Nat) rowUpdated "Remove"
  let remaining : List (Binding Nat Unit) := removed.locals
  check "ActionRowStateFollowsRemoval"
    (removed.value == [20] && remaining[0]?.map (·.value) == some 1)
  let functions : Component [] Nat := .bind (fun n : Nat => n)
    (.button "Use successor" (.set .here (.const (fun n : Nat => n + 1))))
  let functionUpdated ← press (model := Nat) (ModelForm.openState functions 10 Env.nil) "Use successor"
  check "ActionsSupportValuesWithoutCodecs" (functionUpdated.locals.value 41 == 42)
  let focused : Component [] (List Nat) := .bind (0 : Nat) (Component.void <| .focus
    { inputs := inputs[.ui (Ref.here)], run := fun index => .index index .self }
    (.button "Next item" (.set .here {
      inputs := inputs[.ui (Ref.here)], run := fun index => index + 1 })))
  let first := ModelForm.openState focused [10, 20] Env.nil
  let firstKey ← key first "Next item"
  let second ← press (model := List Nat) first "Next item"
  let secondKey ← key second "Next item"
  let stale ← IO.ofExcept (ModelForm.execute (model := List Nat) focused second (.apply firstKey none))
  check "ActionFocusRejectsStaleLocation"
    (firstKey != secondKey && stale.locals.value == 1 &&
      stale.ui.rejection == some (toString InvocationError.absent))
  check "ActionsUseDraftFlushingButtons" (match
      ((ModelView.render counter opened.value {} [] opened.env opened.locals).view.toReact false) with
    | some (.group group) => group.children.any fun
        | .button button => button.onClick == .press (ControlKeyProtocol.toString increment)
        | _ => false
    | _ => false)
  let clicked := ModelForm.openState clicks 0 Env.nil
  let first ← key clicked "Clicked 0"
  let clicked ← press (model := Nat) clicked "Clicked 0"
  check "ActionCaptionsAreComputedWithStableKeys" ((← key clicked "Clicked 1") == first)

end Tests.Actions
