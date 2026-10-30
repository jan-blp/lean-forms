import Forms.ExampleForms.Counter
import Forms.ExampleForms.Basket
import Forms.Runtime.CompositionProtocol
import Forms.Runtime.ActionHistoryProtocol
import Forms.Runtime.Tui

open Forms Forms.Composition Forms.ExampleForms.Basket

#guard (Action.increment (.self : Path .natural .natural)).eval 0 == 1
#guard (Action.decrement (.self : Path .natural .natural)).eval 0 == 0
#guard (Action.decrement (.self : Path .natural .natural)).eval 2 == 1
#guard (Action.set (.self : Path .natural .natural) (.value 7)).eval 2 == 7

private def quantity : Path item .natural := .field .quantity .self
private def bump : Action item := .increment quantity
#guard (bump.eval (line .pen 2)) .product == .pen
#guard (bump.eval (line .pen 2)) .quantity == 3
#guard ((Action.set quantity (.project quantity)).eval (line .pen 2)) .quantity == 2

private def nested : DataType := .record itemFields fun _ => item
private def parent : Path nested item := .field .quantity .self
#guard ((bump.weaken parent).eval (fun _ => line .pen 2)) .quantity .quantity == 3
#guard ((bump.weaken parent).eval (fun _ => line .pen 2)) .product .quantity == 2
#guard (((Action.set quantity (.project quantity)).weaken parent).eval
  (fun _ => line .pen 2)) .quantity .quantity == 2

open Forms.ExampleForms.Counter in
#guard plusFive.eval (fun
  | .current => 2
  | .argument => 0) == 7
open Forms.ExampleForms.Counter in
#guard replace.eval (fun
  | .current => 2
  | .argument => 42) == 42
open Forms.ExampleForms.Counter in
#guard minusOne.eval (fun _ => 0) == 0

private def addArgument : WidgetAction .natural :=
  ⟨"Add amount", .editor .naturalInput
    (.natAdd (.project (.field .current .self)) (.project (.field .argument .self)))⟩
#guard addArgument.eval (fun
  | .current => 5
  | .argument => 3) == 8
#guard (Expr.natSub (.value 3) (.value 7) : Expr .natural .natural).eval 0 == 0

namespace Tests.Actions

open ExampleForms.Counter

private def testHistory : IO Unit := do
  let definitions := ExampleForms.Counter.replayActions
  let initial : ActionHistory .natural CounterAction := ⟨10, #[]⟩
  let first ← IO.ofExcept (ExampleForms.Counter.click initial .plusOne)
  let final ← IO.ofExcept (ExampleForms.Counter.click first .plusFive)
  unless final.value == 16 && final.actions.size == 2 do
    throw (IO.userError "Button application did not record the ordered history")
  let encoded := Runtime.ActionHistoryProtocol.encode actionIds final
  let expected ← IO.ofExcept (Lean.Json.parse
    "{\"value\":\"16\",\"actions\":[\"plusOne\",\"plusFive\"]}")
  unless encoded == expected do throw (IO.userError "Unexpected history wire format")
  let checked ← IO.ofExcept (Runtime.ActionHistoryProtocol.verify actionIds definitions 10 encoded)
  unless checked.value == final.value && Runtime.ActionHistoryProtocol.encode actionIds checked == encoded do
    throw (IO.userError "Replay did not reproduce the submission")
  let empty ← IO.ofExcept (Runtime.ActionHistoryProtocol.verify actionIds definitions 10
    (Runtime.ActionHistoryProtocol.encode actionIds initial))
  unless empty.value == 10 && empty.actions.isEmpty do
    throw (IO.userError "Empty history changed the initial draft")
  for forged in [
      "{\"value\":\"17\",\"actions\":[\"plusOne\",\"plusFive\"]}",
      "{\"value\":\"16\",\"actions\":[\"plusOne\"]}",
      "{\"value\":\"16\",\"actions\":[\"unknown\"]}",
      "{\"value\":\"10\",\"actions\":[\"replace\"]}",
      "{\"value\":\"10\",\"actions\":[{\"action\":\"replace\",\"argument\":false}]}",
      "{\"value\":\"10\",\"actions\":[{\"action\":\"plusOne\",\"argument\":\"1\"}]}",
      "{\"value\":\"10\",\"actions\":[{\"action\":\"replace\",\"argument\":\"10\",\"extra\":true}]}",
      "{\"value\":\"10\"}",
      "{\"value\":\"10\",\"actions\":[42]}",
      "{\"value\":\"10\",\"actions\":[],\"extra\":true}"] do
    let json ← IO.ofExcept (Lean.Json.parse forged)
    unless (Runtime.ActionHistoryProtocol.verify actionIds definitions 10 json).toOption.isNone do
      throw (IO.userError s!"Accepted forged submission: {forged}")
  unless (Runtime.ActionHistoryProtocol.verify actionIds definitions 0 encoded).toOption.isNone do
    throw (IO.userError "Replay accepted the wrong initial draft")
  unless (initial.apply definitions (.button .replace)).toOption.isNone do
    throw (IO.userError "Accepted an editor without its argument")
  let edited ← IO.ofExcept (initial.apply definitions (.editor .replace 42))
  let edited ← IO.ofExcept (edited.apply definitions (.button .plusOne))
  let checked ← IO.ofExcept (Runtime.ActionHistoryProtocol.verify actionIds definitions 10
    (Runtime.ActionHistoryProtocol.encode actionIds edited))
  unless checked.value == 43 && checked.actions.size == 2 do
    throw (IO.userError "Editor argument was not replayed")
  unless (initial.apply definitions (.editor .plusOne 42)).toOption.isNone do
    throw (IO.userError "Button accepted an argument")
  -- Order matters for these buttons.
  let ordered ← IO.ofExcept (ActionHistory.replay
    definitions 0 #[.button .minusOne, .button .plusFive])
  unless ordered.value == 5 do throw (IO.userError "Replay changed action order")
  let repeated ← IO.ofExcept (ActionHistory.replay definitions 0 #[.button .plusOne, .button .plusOne])
  unless repeated.value == 2 && repeated.actions.size == 2 do
    throw (IO.userError "Replay lost a repeated invocation")

private instance : Runtime.MonadTui (ReaderT String (Except IO.Error)) where
  runSpecification _ := read

private def testReturn : IO Unit := do
  let run := Runtime.Tui.runWidget (m := ReaderT String (Except IO.Error))
    (.base .natural) actionIds "Counter" actions 0
  let accepted := "{\"value\":\"43\",\"actions\":[{\"action\":\"replace\",\"argument\":\"42\"},\"plusOne\"]}"
  match run.run accepted with
  | .ok (some result) =>
    unless result.value == 43 && result.actions.size == 2 do
      throw (IO.userError "Lost verified result or history")
  | _ => throw (IO.userError "Rejected valid terminal submission")
  for forged in ["\"43\"", "{\"value\":\"43\",\"actions\":[]}",
      "{\"value\":\"43\",\"actions\":[\"unknown\"]}"] do
    unless (run.run forged).toOption.isNone do
      throw (IO.userError "Accepted forged terminal submission")
  match run.run "null" with
  | .ok none => pure ()
  | _ => throw (IO.userError "Lost terminal cancellation")
  let refined : RefinedDataType .natural := .refine (.base .natural)
    { condition := .natLe (.project .self) (.value 10), errorMessage := "Too large" }
  let restricted := Runtime.Tui.runWidget (m := ReaderT String (Except IO.Error))
    refined actionIds "Counter" actions 0
  unless (restricted.run accepted).toOption.isNone do
    throw (IO.userError "Replay bypassed refinement validation")
  let valueOnly := Runtime.Tui.run (m := ReaderT String (Except IO.Error))
    (.base .natural) form 0
  unless (valueOnly.run "{\"value\":\"43\",\"actions\":[]}").toOption.isNone do
    throw (IO.userError "Value-only API bypassed replay")

def run : IO Unit := do
  testHistory
  testReturn
  let encoded := Runtime.CompositionProtocol.encode (.base .natural) ExampleForms.Counter.form 0
  let expected ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "native/tui/tests/counter.json"))
  let actual ← IO.ofExcept (Lean.Json.parse encoded)
  unless actual == expected do throw (IO.userError "Counter fixture differs from Lean")
  IO.println "PASS: expression actions, button history replay, and counter protocol fixture"

end Tests.Actions
