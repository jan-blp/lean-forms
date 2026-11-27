module

public import Forms.ExampleForms.FillFromDb
public import Forms.Runtime.ModelForm
public import Tests.FreshId
public import Tests.Fetch
meta import Forms.Model.Derive

public section
namespace Tests.Call
open Lean Forms.Model Forms.Model.Sugar Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

structure Tally where
  count : Nat
  log : String
  deriving FormModel

endpoints TallyEndpoint where
  | next : Nat → Nat at "/api/next"

private def note (text : String) : Action [] Tally.Raw :=
  .write path[Tally.Field.log] { inputs := inputs[path[Tally.Field.log]], run := (· ++ text) }

private def count : Computation [] Tally.Raw Nat :=
  { inputs := inputs[path[Tally.Field.count]], run := id }

private def setCount (result : Except String Nat) : Action [] Tally.Raw :=
  match result with
  | .ok next => .write path[Tally.Field.count] (.const next)
  | .error _ => note "!"

def sequenced : Component [] Tally.Raw :=
  .button "Go" <| note "a" * .call TallyEndpoint.next count (fun result => setCount result * note "b") *
    note "c"

def chained : Component [] Tally.Raw :=
  .button "Go" <| .call TallyEndpoint.next count fun first =>
    setCount first * .call TallyEndpoint.next count fun second => setCount second * note "done"

def hideable : Component [] Tally.Raw :=
  .group "Tally" [
    .field path[Tally.Field.count] "Count" .natural,
    .visibleWhen { inputs := inputs[path[Tally.Field.count]], run := fun count => decide (count < 10) }
      (.button "Go" (.call TallyEndpoint.next count fun result => setCount result * note "late"))]

private def layoutRequest : HttpRequest := { method := .get, url := "/layout", body := none }

def revealed : Component [] Tally.Raw := named%
  observe% layout := .loadStatus (data := Bool) (.const (.fetch layoutRequest fromJson?));
  .group "Tally" [
    .field path[Tally.Field.count] "Count" .natural,
    .visibleWhen
      { inputs := inputs[path[Tally.Field.count], ref[layout]]
        run := fun count layout => decide (count < 10) || match layout with
          | .ready shown => shown
          | .loading
          | .failed _ => false }
      (.button "Go" <|
        .call TallyEndpoint.next { inputs := inputs[path[Tally.Field.count]], run := id }
          fun (result : Except String Nat) =>
            .write path[Tally.Field.count] (.const (result.toOption.getD 0)))]

def reacting : Component [] Tally.Raw :=
  .onChange (fun _ _ => .call TallyEndpoint.next count fun (result : Except String Nat) =>
      .write path[Tally.Field.log] (.const (toString (result.toOption.getD 0))))
    (.field path[Tally.Field.count] "Count" .natural)

private def press
  {form : Component [] Tally.Raw}
  (state : ModelForm.State form)
  (label : String)
  (argument : Option Input := none)
  : IO (ModelForm.State form) := do
  let some control := (ModelForm.snapshot form state).controls.find? (·.label == label)
    | throw (IO.userError s!"FAIL no control {label}")
  IO.ofExcept (ModelForm.execute (model := Tally) form state (.apply control.key argument))

private def calls {form : Component [] Tally.Raw} (state : ModelForm.State form) : List HttpCall :=
  state.outbox.filterMap fun effect => match effect with
    | .call call => some call
    | .submit
    | .fetch _
    | .focus _ => none

private def sent {form : Component [] Tally.Raw} (state : ModelForm.State form) : IO HttpCall := do
  let [call] := calls state | throw (IO.userError s!"FAIL expected one call, got {(calls state).length}")
  return call

private def answer
  {form : Component [] Tally.Raw}
  (state : ModelForm.State form)
  (call : HttpCall)
  : IO (ModelForm.State form) := do
  let some body := call.request.body | throw (IO.userError "FAIL call without body")
  let sent : Nat ← IO.ofExcept (Json.parse body >>= fromJson?)
  IO.ofExcept (ModelForm.execute (model := Tally) form state (.called call.id (.ok (toJson (sent + 1)))))

private def disabled {form : Component [] Tally.Raw} (state : ModelForm.State form) : Bool :=
  (ModelForm.snapshot form state).controls.any fun control => control.label == "Go" && control.disabled

private def opened (form : Component [] Tally.Raw) (count : Nat) : ModelForm.State form :=
  ModelForm.openState (model := Tally) form ⟨count, ""⟩ Env.nil supply

def run : IO Unit := do
  let pressed ← press (opened sequenced 1) "Go"
  let call ← sent pressed
  check "CallRunsStepsBeforeIt"
    (pressed.value.log == "a" && call.request.url == "/api/next" && call.request.body == some "1")
  check "CallDisablesButtonWhilePending" (disabled pressed && !disabled (opened sequenced 1))
  let again ← press pressed "Go"
  check "CallRejectsPressWhilePending" (again.ui.rejection.isSome && calls again == [])
  let answered ← answer pressed call
  check "CallContinuesThenRunsRest"
    (answered.value.count == 2 && answered.value.log == "abc" && !disabled answered &&
      calls answered == [])
  let twice ← answer answered call
  check "CallTakesResultOnce" (twice.value.count == 2 && twice.value.log == "abc")
  let failed ← IO.ofExcept (ModelForm.execute (model := Tally) sequenced pressed
    (.called call.id (.error "offline")))
  check "CallPassesFailure" (failed.value.count == 1 && failed.value.log == "a!bc")

  let first ← press (opened chained 1) "Go"
  let second ← answer first (← sent first)
  let secondCall ← sent second
  check "CallChainSendsNext" (second.value.count == 2 && secondCall.request.body == some "2" &&
    disabled second)
  let done ← answer second secondCall
  check "CallChainReplaysResults" (done.value.count == 3 && done.value.log == "done" && !disabled done)

  let started ← press (opened hideable 1) "Go"
  let hiddenCall ← sent started
  let hidden ← press started "Count" (some (.text "50"))
  let dropped ← answer hidden hiddenCall
  check "CallDropsResultWhileHidden" (dropped.value.count == 50 && dropped.value.log == "")
  let shown ← press dropped "Count" (some (.text "1"))
  check "CallReenablesAfterDroppedResult" (!disabled shown)

  let resubmitted ← IO.ofExcept (ModelForm.execute (model := Tally) sequenced answered .submit)
  check "CallAllowsSubmitAfterResult"
    (resubmitted.ui.pending && resubmitted.outbox.contains .submit)

  let opening ← press (opened revealed 1) "Go"
  let revealedCall ← sent opening
  let hiddenAgain ← press opening "Count" (some (.text "50"))
  let submitting ← IO.ofExcept (ModelForm.execute (model := Tally) revealed hiddenAgain .submit)
  let shownAgain ← IO.ofExcept (ModelForm.execute (model := Tally) revealed submitting
    (.loaded (← pendingFetch submitting layoutRequest) (.ok (toJson true))))
  let duringSubmit ← answer shownAgain revealedCall
  let goShown := (ModelForm.snapshot revealed shownAgain).controls.any (·.label == "Go")
  check "CallDoesNotResumeDuringSubmit"
    (submitting.ui.pending && goShown && duringSubmit.value.count == 50 && duringSubmit.ui.pending)

  let reset ← IO.ofExcept (ModelForm.execute (model := Tally) sequenced pressed .reset)
  let afterReset ← answer reset call
  check "CallDroppedByReset" (afterReset.value.log == "" && !disabled afterReset)
  let resetSubmitted ← IO.ofExcept (ModelForm.execute (model := Tally) sequenced reset .submit)
  check "CallDroppedByResetAllowsSubmit" resetSubmitted.ui.pending

  let changed ← press (opened reacting 0) "Count" (some (.text "1"))
  let stale ← sent changed
  let changedAgain ← press changed "Count" (some (.text "5"))
  let latest ← sent changedAgain
  let ignored ← answer changedAgain stale
  check "CallOfSupersededReactionIgnored" (ignored.value.log == "")
  let applied ← answer ignored latest
  check "CallOfLatestReactionApplied" (applied.value.log == "6")
  let appliedSubmitted ← IO.ofExcept (ModelForm.execute (model := Tally) reacting applied .submit)
  check "CallOfSupersededReactionAllowsSubmit" appliedSubmitted.ui.pending

  let fill := FillFromDb.form
  let payee := ModelForm.openState (model := FillFromDb.Payee) fill FillFromDb.initial Env.nil supply
  let some button := (ModelForm.snapshot fill payee).controls.find? (·.label == "Fill from DB")
    | throw (IO.userError "FAIL no Fill from DB button")
  let pending ← IO.ofExcept (ModelForm.execute (model := FillFromDb.Payee) fill payee
    (.apply button.key none))
  let [.call call] := pending.outbox | throw (IO.userError "FAIL Fill from DB sent no call")
  let some response := FillFromDb.serve call.request | throw (IO.userError "FAIL no account")
  let filled ← IO.ofExcept (ModelForm.execute (model := FillFromDb.Payee) fill pending
    (.called call.id (.ok response)))
  check "CallFillsFromDb" (filled.value.iban == "CH93 0076 2011 6238 5295 7")

end Tests.Call
