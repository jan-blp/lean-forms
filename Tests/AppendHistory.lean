import Forms.ExampleForms.Counters
import Forms.Runtime.Tui
import Tests.Weakening

namespace Tests.AppendHistory
open Forms Forms.Composition Forms.Runtime Forms.ExampleForms

private def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

private def append : Component (.list .natural) :=
  .button "Append length" (.append .self (.length (.project .self)))

private def state : DataType := .record Counters.sides fun
  | .left => .natural
  | .right => .list .natural

private def initial : ⟦state⟧
  | .left => 0
  | .right => [7]

private def child : Counters.Side → Component state
  | .left => .field (.field .left .self) "Value" .naturalInput
  | .right => .button "Append value" (.append (.field .right .self) (.project (.field .left .self)))

private def mixed : Component state := .stack (items := Counters.sides) none child

private instance : MonadTui (ReaderT String (Except IO.Error)) where
  runSpecification _ := read

def run : IO Unit := do
  let history ← IO.ofExcept (ComponentHistory.replay append [7] #[.press, .press])
  check "AppendReadsCurrentList" (history.value == [7, 1, 2] && history.actions.size == 2)
  let encoded := ComponentHistoryProtocol.encode history
  let expected ← IO.ofExcept (Lean.Json.parse
    "{\"value\":[\"7\",\"1\",\"2\"],\"actions\":[{\"target\":[],\"action\":\"press\"},{\"target\":[],\"action\":\"press\"}]}")
  check "AppendWireFormat" (encoded == expected)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify append [7] encoded)
  let mixedHistory ← IO.ofExcept (ComponentHistory.replay mixed initial
    #[⟨.left, ⟨.replace, (42 : Nat)⟩⟩, ⟨.right, .press⟩, ⟨.right, .press⟩])
  check "AppendReadsCurrentSibling" (mixedHistory.value .left == 42 && mixedHistory.value .right == [7, 42, 42])
  let reordered := Component.stack (items := Counters.sides) none child (Equiv.swap .left .right)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify reordered initial (ComponentHistoryProtocol.encode mixedHistory))
  let weakened := mixed.weaken (Tests.Weakening.contentPath state)
  let weakenedInitial := Tests.Weakening.wrap initial
  let weakenedHistory ← IO.ofExcept (ComponentHistory.replay weakened weakenedInitial #[⟨.right, .press⟩])
  check "AppendWeakeningPreservesSibling" (weakenedHistory.value .title == "Keep this title")
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify weakened weakenedInitial (ComponentHistoryProtocol.encode weakenedHistory))
  for (entry, expectedError) in [
      ("{\"target\":[],\"action\":\"replace\"}", ComponentHistoryProtocol.Error.unknownAction "replace"),
      ("{\"target\":[],\"action\":\"press\",\"argument\":\"9\"}", .unexpectedArgument),
      ("{\"target\":[\"extra\"],\"action\":\"press\"}", .targetBeyondWidget),
      ("{\"target\":[],\"action\":\"press\",\"extra\":true}", .invalidFields ["target", "action"]),
      ("{\"target\":[],\"action\":\"press\"}", .valueMismatch)] do
    let entry ← IO.ofExcept (Lean.Json.parse entry)
    let submission := Lean.Json.mkObj [("value", Lean.toJson ([] : List String)), ("actions", Lean.Json.arr #[entry])]
    check "RejectInvalidAppendSubmission" (match ComponentHistoryProtocol.verify append [] submission with
      | .error error => error == expectedError
      | .ok _ => false)
  let visible := Component.visibleWhen (.natLe (.length (.project .self)) (.value 1)) append
  let disabled := Component.disabledWhen (.natLe (.value 2) (.length (.project .self))) append
  for (component, expectedError) in [(visible, Component.InvocationError.hidden), (disabled, .disabled)] do
    check "RejectUnavailableAppend" (match ComponentHistoryProtocol.verify component [7] expected with
      | .error error => error == .invocation expectedError
      | .ok _ => false)
  let result ← IO.ofExcept ((Tui.run (m := ReaderT String (Except IO.Error))
    (.base (.list .natural)) append [7]).run encoded.compress)
  check "TuiReturnsAppendHistory" (result.any fun result => result.value == [7, 1, 2] && result.actions.map Array.size == some 2)
  IO.println "PASS: append history, current state, targets, conditions, and decoding"

end Tests.AppendHistory
