import Forms.ExampleForms.Counters
import Forms.Runtime.Tui
import Tests.Weakening

namespace Tests.ComponentHistory
open Forms Forms.Composition Forms.Runtime Forms.ExampleForms

private def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

private def reordered : Component Counters.state :=
  .stack (items := Counters.sides) (some "Counters") Counters.widget (Equiv.swap .left .right)

private def nested : Component Counters.state :=
  .stack (items := Counters.sides) none (fun _ => Counters.form)

private def shared : Component .natural :=
  .stack (items := Counters.sides) none (fun
    | .left => Counter.form
    | .right => .actionWidget (ids := Counter.actionIds) .self "Counter" (fun _ => Counter.plusFive))

private def mixedState : DataType := .record Counters.sides fun
  | .left => .natural
  | .right => .text

private def mixed : Component mixedState :=
  .stack (items := Counters.sides) none (fun
    | .left => .actionWidget (ids := Counter.actionIds) (.field .left .self) "Number" Counter.actions
    | .right => .actionWidget (ids := Counter.actionIds) (.field .right .self) "Text"
        (fun _ => ⟨"Replace", .editor .textInput (.project (.field .argument .self))⟩))

private instance : MonadTui (ReaderT String (Except IO.Error)) where
  runSpecification _ := read

def run : IO Unit := do
  let actions : Array Counters.form.Invocation := #[
    ⟨.left, ⟨.plusOne, ()⟩⟩,
    ⟨.right, ⟨.plusFive, ()⟩⟩,
    ⟨.left, ⟨.replace, (42 : Nat)⟩⟩,
    ⟨.right, ⟨.minusOne, ()⟩⟩]
  let replayed := Composition.ComponentHistory.replay Counters.form Counters.initial actions
  check "IndependentWidgetTargets" (replayed.value .left == 42 && replayed.value .right == 14)
  let encoded := ComponentHistoryProtocol.encode replayed
  let checked ← IO.ofExcept (ComponentHistoryProtocol.verify Counters.form Counters.initial encoded)
  check "ComponentHistoryRoundTrip" (ComponentHistoryProtocol.encode checked == encoded)
  let reorderedResult ← IO.ofExcept (ComponentHistoryProtocol.verify reordered Counters.initial encoded)
  check "DisplayOrderPreservesTargets" (ComponentHistoryProtocol.encode reorderedResult == encoded)
  let nestedResult := Composition.ComponentHistory.replay nested Counters.initial
    #[⟨.right, ⟨.left, ⟨.plusOne, ()⟩⟩⟩]
  let nestedJson := ComponentHistoryProtocol.encode nestedResult
  let target ← IO.ofExcept (nestedJson.getObjVal? "actions" >>= fun actions =>
    actions.getArr? >>= fun actions => actions[0]!.getObjVal? "target")
  check "NestedTargetEncoding" (target == Lean.toJson (["right", "left"] : List String))
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify nested Counters.initial nestedJson)
  let sharedResult := Composition.ComponentHistory.replay shared 0
    #[⟨.left, ⟨.plusOne, ()⟩⟩, ⟨.right, ⟨.plusOne, ()⟩⟩]
  check "SamePathDifferentDefinitions" (sharedResult.value == 6)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify shared 0 (ComponentHistoryProtocol.encode sharedResult))
  let mixedInitial : ⟦mixedState⟧ := fun
    | .left => 0
    | .right => "old"
  let mixedResult := Composition.ComponentHistory.replay mixed mixedInitial
    #[⟨.left, ⟨.plusOne, ()⟩⟩, ⟨.right, ⟨.replace, "new"⟩⟩]
  check "WidgetArgumentTypes" (mixedResult.value .left == 1 && mixedResult.value .right == "new")
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify mixed mixedInitial (ComponentHistoryProtocol.encode mixedResult))
  let weakened := Counters.form.weaken (Tests.Weakening.contentPath Counters.state)
  let weakenedInitial := Tests.Weakening.wrap Counters.initial
  let weakenedValue := Tests.Weakening.wrap replayed.value
  let weakenedJson := Lean.Json.mkObj [
    ("value", JsonProtocol.valueToJson weakenedValue),
    ("actions", ← IO.ofExcept (encoded.getObjVal? "actions"))]
  let weakenedResult ← IO.ofExcept (ComponentHistoryProtocol.verify weakened weakenedInitial weakenedJson)
  check "WeakeningPreservesSibling" (weakenedResult.value .title == "Keep this title")
  for entry in [
      "{\"target\":[\"missing\"],\"action\":\"plusOne\"}",
      "{\"target\":[],\"action\":\"plusOne\"}",
      "{\"target\":[\"left\",\"extra\"],\"action\":\"plusOne\"}",
      "{\"target\":[0],\"action\":\"plusOne\"}",
      "{\"target\":[\"left\"],\"action\":\"missing\"}",
      "{\"target\":[\"left\"],\"action\":\"replace\"}",
      "{\"target\":[\"left\"],\"action\":\"replace\",\"argument\":true}",
      "{\"target\":[\"left\"],\"action\":\"plusOne\",\"argument\":\"1\"}",
      "{\"target\":[\"left\"],\"action\":\"plusOne\",\"extra\":true}"] do
    let json ← IO.ofExcept (Lean.Json.parse entry)
    let submission := Lean.Json.mkObj [("value", JsonProtocol.valueToJson Counters.initial),
      ("actions", Lean.Json.arr #[json])]
    check "RejectMalformedInvocation" (ComponentHistoryProtocol.verify Counters.form Counters.initial submission).toOption.isNone
  let forged := Lean.Json.mkObj [("value", JsonProtocol.valueToJson Counters.initial),
    ("actions", ← IO.ofExcept (encoded.getObjVal? "actions"))]
  check "RejectForgedFinalValue" (ComponentHistoryProtocol.verify Counters.form Counters.initial forged).toOption.isNone
  let result ← IO.ofExcept ((Tui.run (m := ReaderT String (Except IO.Error))
    (.base Counters.state) Counters.form Counters.initial).run encoded.compress)
  check "TuiReturnsComponentHistory" (result.any fun result =>
    result.value .left == 42 && result.actions.map Array.size == some 4)
  let unsupported : Component Counters.state := .stack (items := Counters.sides) none (fun
    | .left => Counters.widget .left
    | .right => .field (.field .right .self) "Right" .naturalInput)
  check "MixedLegacyFormIsExplicit" (!unsupported.supportsHistory)
  let result ← IO.ofExcept ((Tui.run (m := ReaderT String (Except IO.Error))
    (.base Counters.state) unsupported Counters.initial).run (JsonProtocol.valueToJson Counters.initial).compress)
  check "LegacyHistoryIsUnavailable" (result.any fun result => result.actions.isNone)
  let expected ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "native/tui/tests/counters.json"))
  let actual ← IO.ofExcept (Lean.Json.parse (CompositionProtocol.encode (.base Counters.state) Counters.form Counters.initial))
  check "CountersFixture" (actual == expected)
  IO.println "PASS: component targets, replay, display order, weakening, and legacy results"

end Tests.ComponentHistory
