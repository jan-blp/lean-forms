import Forms.ExampleForms.Counter
import Forms.ExampleForms.Basket
import Forms.Runtime.CompositionProtocol
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

example : True := by
  fail_if_success have : form.Invocation := ⟨.replace, ()⟩
  fail_if_success have : form.Invocation := ⟨.plusOne, (42 : Nat)⟩
  fail_if_success have : form.Invocation := ⟨.replace, "42"⟩
  trivial

private def addDefinitions : Unit → Action.Presentation .natural := fun _ => addArgument.presentation
private def addInvocation : Action.Invocation addDefinitions := ⟨(), (3 : Nat)⟩
#guard addInvocation.apply 5 == 8

private def testDecodeErrors : IO Unit := do
  let cases : List (Runtime.ComponentHistoryProtocol.Error × String) := [
    (.missingArgument, "{\"target\":[],\"action\":\"replace\"}"),
    (.unexpectedArgument, "{\"target\":[],\"action\":\"plusOne\",\"argument\":null}"),
    (.unknownAction "missing", "{\"target\":[],\"action\":\"missing\"}"),
    (.targetBeyondWidget, "{\"target\":[\"extra\"],\"action\":\"plusOne\"}"),
    (.invalidFields ["target", "action"], "{\"target\":[],\"action\":\"plusOne\",\"extra\":true}"),
    (.valueMismatch, "{\"target\":[],\"action\":\"plusOne\"}")]
  for (expected, entry) in cases do
    let invocation ← IO.ofExcept (Lean.Json.parse entry)
    let submission := Lean.Json.mkObj [
      ("value", Lean.toJson "10"), ("actions", Lean.Json.arr #[invocation])]
    match Runtime.ComponentHistoryProtocol.verify form 10 submission with
    | .error actual =>
      unless actual == expected do throw (IO.userError s!"Expected {repr expected}, got {repr actual}")
    | .ok _ => throw (IO.userError "Expected a typed decoding error")

private def testHistory : IO Unit := do
  let initial : ComponentHistory form := ⟨10, #[]⟩
  let first := initial.apply ⟨.plusOne, ()⟩
  let final := first.apply ⟨.plusFive, ()⟩
  unless final.value == 16 && final.actions.size == 2 do
    throw (IO.userError "Button application did not record the ordered history")
  let encoded := Runtime.ComponentHistoryProtocol.encode final
  let expected ← IO.ofExcept (Lean.Json.parse
    "{\"value\":\"16\",\"actions\":[{\"target\":[],\"action\":\"plusOne\"},{\"target\":[],\"action\":\"plusFive\"}]}")
  unless encoded == expected do throw (IO.userError "Unexpected history wire format")
  let checked ← IO.ofExcept (Runtime.ComponentHistoryProtocol.verify form 10 encoded)
  unless checked.value == final.value && Runtime.ComponentHistoryProtocol.encode checked == encoded do
    throw (IO.userError "Replay did not reproduce the submission")
  let empty ← IO.ofExcept (Runtime.ComponentHistoryProtocol.verify form 10
    (Runtime.ComponentHistoryProtocol.encode initial))
  unless empty.value == 10 && empty.actions.isEmpty do
    throw (IO.userError "Empty history changed the initial draft")
  for forged in [
      "{\"value\":\"17\",\"actions\":[{\"target\":[],\"action\":\"plusOne\"},{\"target\":[],\"action\":\"plusFive\"}]}",
      "{\"value\":\"16\",\"actions\":[{\"target\":[],\"action\":\"plusOne\"}]}",
      "{\"value\":\"16\",\"actions\":[{\"target\":[],\"action\":\"unknown\"}]}",
      "{\"value\":\"10\",\"actions\":[{\"target\":[],\"action\":\"replace\"}]}",
      "{\"value\":\"10\",\"actions\":[{\"target\":[],\"action\":\"replace\",\"argument\":false}]}",
      "{\"value\":\"10\",\"actions\":[{\"target\":[],\"action\":\"plusOne\",\"argument\":\"1\"}]}",
      "{\"value\":\"10\",\"actions\":[{\"target\":[],\"action\":\"replace\",\"argument\":\"10\",\"extra\":true}]}",
      "{\"value\":\"10\"}",
      "{\"value\":\"10\",\"actions\":[42]}",
      "{\"value\":\"10\",\"actions\":[],\"extra\":true}"] do
    let json ← IO.ofExcept (Lean.Json.parse forged)
    unless (Runtime.ComponentHistoryProtocol.verify form 10 json).toOption.isNone do
      throw (IO.userError s!"Accepted forged submission: {forged}")
  unless (Runtime.ComponentHistoryProtocol.verify form 0 encoded).toOption.isNone do
    throw (IO.userError "Replay accepted the wrong initial draft")
  let edited := initial.apply ⟨.replace, (42 : Nat)⟩
  let edited := edited.apply ⟨.plusOne, ()⟩
  let checked ← IO.ofExcept (Runtime.ComponentHistoryProtocol.verify form 10
    (Runtime.ComponentHistoryProtocol.encode edited))
  unless checked.value == 43 && checked.actions.size == 2 do
    throw (IO.userError "Editor argument was not replayed")
  -- Order matters for these buttons.
  let ordered := ComponentHistory.replay
    form 0 #[⟨.minusOne, ()⟩, ⟨.plusFive, ()⟩]
  unless ordered.value == 5 do throw (IO.userError "Replay changed action order")
  let repeated := ComponentHistory.replay form 0 #[⟨.plusOne, ()⟩, ⟨.plusOne, ()⟩]
  unless repeated.value == 2 && repeated.actions.size == 2 do
    throw (IO.userError "Replay lost a repeated invocation")

private instance : Runtime.MonadTui (ReaderT String (Except IO.Error)) where
  runSpecification _ := read

private def testReturn : IO Unit := do
  let run := Runtime.Tui.run (m := ReaderT String (Except IO.Error))
    (.base .natural) form 0
  let accepted := "{\"value\":\"43\",\"actions\":[{\"target\":[],\"action\":\"replace\",\"argument\":\"42\"},{\"target\":[],\"action\":\"plusOne\"}]}"
  match run.run accepted with
  | .ok (some result) =>
    unless result.value == 43 && (result.actions.map Array.size) == some 2 do
      throw (IO.userError "Lost verified result or history")
  | .ok none => throw (IO.userError "Rejected valid terminal submission")
  | .error error => throw error
  for forged in ["\"43\"", "{\"value\":\"43\",\"actions\":[]}",
      "{\"value\":\"43\",\"actions\":[{\"target\":[],\"action\":\"unknown\"}]}"] do
    unless (run.run forged).toOption.isNone do
      throw (IO.userError "Accepted forged terminal submission")
  match run.run "null" with
  | .ok none => pure ()
  | .ok (some _) => throw (IO.userError "Lost terminal cancellation")
  | .error error => throw error
  let refined : RefinedDataType .natural := .refine (.base .natural)
    { condition := .natLe (.project .self) (.value 10), errorMessage := "Too large" }
  let restricted := Runtime.Tui.run (m := ReaderT String (Except IO.Error))
    refined form 0
  unless (restricted.run accepted).toOption.isNone do
    throw (IO.userError "Replay bypassed refinement validation")

def run : IO Unit := do
  testHistory
  testDecodeErrors
  testReturn
  let encoded := Runtime.CompositionProtocol.encode (.base .natural) ExampleForms.Counter.form 0
  let expected ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "native/tui/tests/counter.json"))
  let actual ← IO.ofExcept (Lean.Json.parse encoded)
  unless actual == expected do throw (IO.userError "Counter fixture differs from Lean")
  IO.println "PASS: expression actions, button history replay, and counter protocol fixture"

end Tests.Actions
