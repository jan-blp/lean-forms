module

public import Forms.ExampleForms.Counters
public import Forms.Runtime.CompiledView
public import Forms.Runtime.ComponentHistoryProtocol
public import Tests.Weakening

@[expose] public section

namespace Tests.ButtonHistory
open Forms Forms.Composition Forms.Runtime Forms.ExampleForms

def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

def increment : Component .natural := .button "Increment" (.increment .self)

def child : Counters.Side → Component Counters.state
  | .left => .field (.field .left .self) "Left" .naturalInput
  | .right => .button "Copy left" (.set (.field .right .self) (.project (.field .left .self)))

def mixed : Component Counters.state := .stack (items := Counters.sides) none child

example {state element : DataType}
  (target : Path state (.list element))
  (value : Expr state element)
  : Action.append target value = .set target (.snoc (.project target) value) := rfl

def appendState : DataType := .record Counters.sides fun
  | .left => .natural
  | .right => .list .natural

def appendInitial : ⟦appendState⟧
  | .left => 0
  | .right => [7]

def appendMixed : Component appendState := .stack (items := Counters.sides) none fun
  | .left => .field (.field .left .self) "Value" .naturalInput
  | .right => .button "Append value" (.append (.field .right .self) (.project (.field .left .self)))

def run : IO Unit := do
  let history ← IO.ofExcept (ComponentHistory.replay increment 0 #[.press, .press])
  check "RepeatedButtonPresses" (history.value == 2 && history.actions.size == 2)
  let encoded := ComponentHistoryProtocol.encode history
  let expected ← IO.ofExcept (Lean.Json.parse
    "{\"value\":\"2\",\"actions\":[{\"target\":[],\"action\":\"press\"},{\"target\":[],\"action\":\"press\"}]}")
  check "ButtonWireFormat" (encoded == expected)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify increment 0 encoded)
  let decrement := Component.button "Decrement" (Action.decrement Path.self)
  let unchanged ← IO.ofExcept (ComponentHistory.replay decrement 0 #[.press, .press])
  check "NoOpPressesAreRecorded" (unchanged.value == 0 && unchanged.actions.size == 2)
  let result ← IO.ofExcept (ComponentHistory.replay mixed Counters.initial
    #[⟨.left, ⟨.replace, (42 : Nat)⟩⟩, ⟨.right, .press⟩])
  check "ButtonReadsCurrentSibling" (result.value .left == 42 && result.value .right == 42)
  let appended ← IO.ofExcept (ComponentHistory.replay appendMixed appendInitial
    #[⟨.left, ⟨.replace, (42 : Nat)⟩⟩, ⟨.right, .press⟩, ⟨.right, .press⟩])
  check "AppendReadsCurrentSibling" (appended.value .left == 42 && appended.value .right == [7, 42, 42])
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
      ("{\"target\":[],\"action\":\"press\",\"extra\":true}", .invalidFields ["target", "action"])] do
    let entry ← IO.ofExcept (Lean.Json.parse entry)
    let submission := Lean.Json.mkObj [("value", Lean.toJson "0"), ("actions", Lean.Json.arr #[entry])]
    check "RejectInvalidButtonSubmission" (match ComponentHistoryProtocol.verify increment 0 submission with
      | .error error => error == expectedError
      | .ok _ => false)
  IO.println "PASS: button and append history, targets, and decoding"

end Tests.ButtonHistory
