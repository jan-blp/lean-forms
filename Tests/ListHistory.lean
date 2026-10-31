import Forms.ExampleForms.Counters
import Forms.ExampleForms.Shapes
import Forms.Runtime.Tui
import Tests.Weakening

namespace Tests.ListHistory
open Forms Forms.Composition Forms.Runtime Forms.ExampleForms

private def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

private def form : Component (.list .natural) :=
  .list .self "Numbers" (.field .self "Value" .naturalInput) 7

private instance : MonadTui (ReaderT String (Except IO.Error)) where
  runSpecification _ := read

def run : IO Unit := do
  let actions : Array form.Invocation := #[
    .appendDefault, .item 2 ⟨.replace, (30 : Nat)⟩, .remove 0, .item 0 ⟨.replace, (21 : Nat)⟩]
  let history ← IO.ofExcept (ComponentHistory.replay form [10, 20] actions)
  check "ListIndicesFollowCurrentState" (history.value == [21, 30] && history.actions.size == 4)
  let encoded := ComponentHistoryProtocol.encode history
  let expected ← IO.ofExcept (Lean.Json.parse
    "{\"value\":[\"21\",\"30\"],\"actions\":[{\"target\":[],\"action\":\"appendDefault\"},{\"target\":[2],\"action\":\"replace\",\"argument\":\"30\"},{\"target\":[],\"action\":\"remove\",\"index\":0},{\"target\":[0],\"action\":\"replace\",\"argument\":\"21\"}]}")
  check "ListWireFormat" (encoded == expected)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify form [10, 20] encoded)
  let defaults ← IO.ofExcept (ComponentHistory.replay form [] #[.appendDefault, .appendDefault])
  check "ListUsesDeclaredDefault" (defaults.value == [7, 7])
  let removed ← IO.ofExcept (ComponentHistory.replay form [10, 20] #[.remove 1, .remove 0])
  check "RemoveLastAndOnlyItem" removed.value.isEmpty
  for (initial, actions, expectedError) in [
      ([], #[Action.List.remove 0], Component.InvocationError.indexOutOfBounds 0 0),
      ([1], #[.remove 1], .indexOutOfBounds 1 1),
      ([1], #[.item 1 ⟨.replace, (2 : Nat)⟩], .indexOutOfBounds 1 1),
      ([1], #[.remove 0, .item 0 ⟨.replace, (2 : Nat)⟩], .indexOutOfBounds 0 0)] do
    check "ListBoundsCheckedDuringReplay" (match ComponentHistory.replay form initial actions with
      | .error error => error == expectedError
      | .ok _ => false)
  let nested := Component.list Path.self "Groups" form []
  let nestedHistory ← IO.ofExcept (ComponentHistory.replay nested [[1], [2]]
    #[.remove 0, .item 0 .appendDefault, .item 0 (.item 1 ⟨.replace, (9 : Nat)⟩)])
  check "NestedListHistory" (nestedHistory.value == [[2, 9]])
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify nested [[1], [2]] (ComponentHistoryProtocol.encode nestedHistory))
  let counters := Component.list Path.self "Counters" Counters.form Counters.initial
  let countersHistory ← IO.ofExcept (ComponentHistory.replay counters []
    #[.appendDefault, .item 0 ⟨.right, ⟨.plusFive, ()⟩⟩])
  check "ListChildUsesLocalState" (countersHistory.value.head?.any fun value => value .right == 15)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify counters [] (ComponentHistoryProtocol.encode countersHistory))
  let weakened := form.weaken (Tests.Weakening.contentPath (.list .natural))
  let initial := Tests.Weakening.wrap [10, 20]
  let result ← IO.ofExcept (ComponentHistory.replay weakened initial actions)
  check "ListWeakeningPreservesSibling" (result.value .title == "Keep this title")
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify weakened initial (ComponentHistoryProtocol.encode result))
  for entry in [
      "{\"target\":[],\"action\":\"appendDefault\",\"argument\":\"42\"}",
      "{\"target\":[],\"action\":\"remove\"}",
      "{\"target\":[],\"action\":\"remove\",\"index\":-1}",
      "{\"target\":[],\"action\":\"remove\",\"index\":0.5}",
      "{\"target\":[],\"action\":\"remove\",\"index\":\"0\"}",
      "{\"target\":[\"0\"],\"action\":\"replace\",\"argument\":\"1\"}",
      "{\"target\":[-1],\"action\":\"replace\",\"argument\":\"1\"}",
      "{\"target\":[0.5],\"action\":\"replace\",\"argument\":\"1\"}",
      "{\"target\":[],\"action\":\"add\",\"argument\":\"1\"}"] do
    let entry ← IO.ofExcept (Lean.Json.parse entry)
    check "RejectMalformedListAction" (ComponentHistoryProtocol.verify form [1]
      (Lean.Json.mkObj [("value", Lean.toJson (["1"] : List String)), ("actions", Lean.Json.arr #[entry])])).toOption.isNone
  let disabled := Component.disabledWhen (Expr.value true) form
  for action in ([.appendDefault, .remove 0, .item 0 ⟨.replace, (2 : Nat)⟩] : List form.Invocation) do
    check "DisabledListRejectsAllActions" (match disabled.applyInvocation [1] action with
      | .error error => error == .disabled
      | .ok _ => false)
  let hiddenChild := Component.list Path.self "Numbers"
    (Component.visibleWhen (Expr.value false) (Component.field Path.self "Value" Widget.naturalInput)) 7
  check "HiddenChildCannotBeEdited" (match hiddenChild.applyInvocation [1] (.item 0 ⟨.replace, (2 : Nat)⟩) with
    | .error error => error == .hidden
    | .ok _ => false)
  let _ ← IO.ofExcept (hiddenChild.applyInvocation [1] (.remove 0))
  let unsupported := Component.list Path.self "Shapes" Shapes.form Shapes.draft
  check "ListWithSumRemainsLegacy" (!unsupported.supportsHistory)
  let result ← IO.ofExcept ((Tui.run (m := ReaderT String (Except IO.Error))
    (.base (.list .natural)) form [10, 20]).run encoded.compress)
  check "TuiReturnsListHistory" (result.any fun result => result.value == [21, 30] && result.actions.map Array.size == some 4)
  IO.println "PASS: list history, shifting indices, bounds, nested targets, and decoding"

end Tests.ListHistory
