import Forms.ExampleForms.Counters
import Forms.Runtime.Tui
import Tests.Weakening

namespace Tests.ButtonHistory
open Forms Forms.Composition Forms.Runtime Forms.ExampleForms

private def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

private def increment : Component .natural := .button "Increment" (.increment .self)

private def child : Counters.Side → Component Counters.state
  | .left => .field (.field .left .self) "Left" .naturalInput
  | .right => .button "Copy left" (.set (.field .right .self) (.project (.field .left .self)))

private def mixed : Component Counters.state := .stack (items := Counters.sides) none child

private instance : MonadTui (ReaderT String (Except IO.Error)) where
  runSpecification _ := read

def run : IO Unit := do
  let history ← IO.ofExcept (ComponentHistory.replay increment 0 #[.press, .press])
  check "RepeatedButtonPresses" (history.value == 2 && history.actions.size == 2)
  let encoded := ComponentHistoryProtocol.encode history
  let expected ← IO.ofExcept (Lean.Json.parse
    "{\"value\":\"2\",\"actions\":[{\"target\":[],\"action\":\"press\"},{\"target\":[],\"action\":\"press\"}]}")
  check "ButtonWireFormat" (encoded == expected)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify increment 0 encoded)
  let empty : ComponentHistory increment := ⟨0, #[]⟩
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify increment 0 (ComponentHistoryProtocol.encode empty))
  let decrement := Component.button "Decrement" (Action.decrement Path.self)
  let unchanged ← IO.ofExcept (ComponentHistory.replay decrement 0 #[.press, .press])
  check "NoOpPressesAreRecorded" (unchanged.value == 0 && unchanged.actions.size == 2)
  let result ← IO.ofExcept (ComponentHistory.replay mixed Counters.initial
    #[⟨.left, ⟨.replace, (42 : Nat)⟩⟩, ⟨.right, .press⟩])
  check "ButtonReadsCurrentSibling" (result.value .left == 42 && result.value .right == 42)
  let encodedMixed := ComponentHistoryProtocol.encode result
  let reordered := Component.stack (items := Counters.sides) none child (Equiv.swap .left .right)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify reordered Counters.initial encodedMixed)
  let nested := Component.stack (items := Counters.sides) none (fun _ => mixed)
  let nestedHistory ← IO.ofExcept (ComponentHistory.replay nested Counters.initial #[⟨.right, ⟨.right, .press⟩⟩])
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify nested Counters.initial (ComponentHistoryProtocol.encode nestedHistory))
  let weakened := mixed.weaken (Tests.Weakening.contentPath Counters.state)
  let initial := Tests.Weakening.wrap Counters.initial
  let weakenedHistory ← IO.ofExcept (ComponentHistory.replay weakened initial #[⟨.right, .press⟩])
  check "ButtonWeakeningPreservesSibling" (weakenedHistory.value .title == "Keep this title")
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify weakened initial (ComponentHistoryProtocol.encode weakenedHistory))
  for (entry, expectedError) in [
      ("{\"target\":[],\"action\":\"replace\"}", ComponentHistoryProtocol.Error.unknownAction "replace"),
      ("{\"target\":[],\"action\":\"press\",\"argument\":null}", .unexpectedArgument),
      ("{\"target\":[\"extra\"],\"action\":\"press\"}", .targetBeyondWidget),
      ("{\"target\":[],\"action\":\"press\",\"extra\":true}", .invalidFields ["target", "action"]),
      ("{\"target\":[],\"action\":\"press\"}", .valueMismatch)] do
    let entry ← IO.ofExcept (Lean.Json.parse entry)
    let submission := Lean.Json.mkObj [("value", Lean.toJson "0"), ("actions", Lean.Json.arr #[entry])]
    check "RejectInvalidButtonSubmission" (match ComponentHistoryProtocol.verify increment 0 submission with
      | .error error => error == expectedError
      | .ok _ => false)
  let visible := Component.visibleWhen (.natLe (.project .self) (.value 0)) increment
  let disabled := Component.disabledWhen (.natLe (.value 1) (.project .self)) increment
  for (component, expectedError) in [(visible, Component.InvocationError.hidden), (disabled, .disabled)] do
    check "RejectUnavailableButtonPress" (match ComponentHistoryProtocol.verify component 0 expected with
      | .error error => error == .invocation expectedError
      | .ok _ => false)
  let result ← IO.ofExcept ((Tui.run (m := ReaderT String (Except IO.Error))
    (.base .natural) increment 0).run encoded.compress)
  check "TuiReturnsButtonHistory" (result.any fun result => result.value == 2 && result.actions.map Array.size == some 2)
  IO.println "PASS: standalone button history, targets, conditions, and decoding"

end Tests.ButtonHistory
