module

public import Batteries.Data.Except

public import Forms.ExampleForms.Counters
public import Forms.ExampleForms.Shapes
public import Forms.Runtime.CompiledView
public import Forms.Runtime.ComponentHistoryProtocol
public import Tests.Weakening

@[expose] public section

namespace Tests.ComponentHistory
open Forms Forms.Composition Forms.Runtime Forms.ExampleForms

def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

def reordered : Component Counters.state :=
  .stack (items := Counters.sides) (some "Counters") Counters.widget (Equiv.swap .left .right)

def nested : Component Counters.state :=
  .stack (items := Counters.sides) none (fun _ => Counters.form)

def shared : Component .natural :=
  .stack (items := Counters.sides) none (fun
    | .left => Counter.form
    | .right => .actionWidget (ids := Counter.actionIds) .self "Counter" (fun _ => Counter.plusFive))

def mixedState : DataType := .record Counters.sides fun
  | .left => .natural
  | .right => .text

def mixed : Component mixedState :=
  .stack (items := Counters.sides) none (fun
    | .left => .actionWidget (ids := Counter.actionIds) (.field .left .self) "Number" Counter.actions
    | .right => .actionWidget (ids := Counter.actionIds) (.field .right .self) "Text"
        (fun _ => ⟨"Replace", .editor .textInput (.project (.field .argument .self))⟩))

def visible : Component .natural :=
  .visibleWhen (.natLe (.project .self) (.value 0)) Counter.form

def disabled : Component .natural :=
  .disabledWhen (.natLe (.value 1) (.project .self)) Counter.form

def conditionalStack : Component .natural :=
  .stack (items := Counters.sides) none (fun
    | .left => .visibleWhen (.natLe (.project .self) (.value 0)) disabled
    | .right => Counter.form)

def testConditions : IO Unit := do
  for result in [visible.applyInvocation 1 ⟨.plusOne, ()⟩,
      visible.applyInvocation 1 ⟨.replace, (0 : Nat)⟩] do
    check "HiddenActionRejected" (result == .error .hidden)
  check "DisabledActionRejected" (disabled.applyInvocation 1 ⟨.plusOne, ()⟩ == .error .disabled)
  let visibleResult ← IO.ofExcept (ComponentHistory.replay visible 0 #[⟨.plusOne, ()⟩])
  let disabledResult ← IO.ofExcept (ComponentHistory.replay disabled 0 #[⟨.plusOne, ()⟩])
  check "ActionCanHideItself" (visibleResult.value == 1)
  check "ActionCanDisableItself" (disabledResult.value == 1)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify visible 0 (ComponentHistoryProtocol.encode visibleResult))
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify disabled 0 (ComponentHistoryProtocol.encode disabledResult))
  let forged ← IO.ofExcept (Lean.Json.parse
    "{\"value\":\"2\",\"actions\":[{\"target\":[],\"action\":\"plusOne\"},{\"target\":[],\"action\":\"plusOne\"}]}")
  check "ReplayChecksCurrentVisibility"
    (match ComponentHistoryProtocol.verify visible 0 forged with
      | .error error => error == .invocation .hidden
      | .ok _ => false)
  check "ReplayChecksCurrentEnabledState"
    (match ComponentHistoryProtocol.verify disabled 0 forged with
      | .error error => error == .invocation .disabled
      | .ok _ => false)
  let restored ← IO.ofExcept (ComponentHistory.replay conditionalStack 0 #[
    ⟨.left, ⟨.plusOne, ()⟩⟩,
    ⟨.right, ⟨.minusOne, ()⟩⟩,
    ⟨.left, ⟨.plusOne, ()⟩⟩])
  check "SiblingRestoresAvailability" (restored.value == 1 && restored.actions.size == 3)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify conditionalStack 0 (ComponentHistoryProtocol.encode restored))
  let wrappedStack := Component.disabledWhen (Expr.value false) conditionalStack
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify wrappedStack 0 (ComponentHistoryProtocol.encode restored))
  let weakened := visible.weaken (Tests.Weakening.contentPath .natural)
  check "ConditionalWeakeningChecksLocalState"
    ((weakened.applyInvocation (Tests.Weakening.wrap 1) ⟨.plusOne, ()⟩).toOption.isNone)

def run : IO Unit := do
  testConditions
  let actions : Array Counters.form.Invocation := #[
    ⟨.left, ⟨.plusOne, ()⟩⟩,
    ⟨.right, ⟨.plusFive, ()⟩⟩,
    ⟨.left, ⟨.replace, (42 : Nat)⟩⟩,
    ⟨.right, ⟨.minusOne, ()⟩⟩]
  let replayed ← IO.ofExcept (Composition.ComponentHistory.replay Counters.form Counters.initial actions)
  check "IndependentWidgetTargets" (replayed.value .left == 42 && replayed.value .right == 14)
  let encoded := ComponentHistoryProtocol.encode replayed
  let checked ← IO.ofExcept (ComponentHistoryProtocol.verify Counters.form Counters.initial encoded)
  check "ComponentHistoryRoundTrip" (ComponentHistoryProtocol.encode checked == encoded)
  let reorderedResult ← IO.ofExcept (ComponentHistoryProtocol.verify reordered Counters.initial encoded)
  check "DisplayOrderPreservesTargets" (ComponentHistoryProtocol.encode reorderedResult == encoded)
  let nestedResult ← IO.ofExcept (Composition.ComponentHistory.replay nested Counters.initial
    #[⟨.right, ⟨.left, ⟨.plusOne, ()⟩⟩⟩])
  let nestedJson := ComponentHistoryProtocol.encode nestedResult
  let target ← IO.ofExcept (nestedJson.getObjVal? "actions" >>= fun actions =>
    actions.getArr? >>= fun actions => actions[0]!.getObjVal? "target")
  check "NestedTargetEncoding" (target == Lean.toJson (["right", "left"] : List String))
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify nested Counters.initial nestedJson)
  let sharedResult ← IO.ofExcept (Composition.ComponentHistory.replay shared 0
    #[⟨.left, ⟨.plusOne, ()⟩⟩, ⟨.right, ⟨.plusOne, ()⟩⟩])
  check "SamePathDifferentDefinitions" (sharedResult.value == 6)
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify shared 0 (ComponentHistoryProtocol.encode sharedResult))
  let mixedInitial : ⟦mixedState⟧ := fun
    | .left => 0
    | .right => "old"
  let mixedResult ← IO.ofExcept (Composition.ComponentHistory.replay mixed mixedInitial
    #[⟨.left, ⟨.plusOne, ()⟩⟩, ⟨.right, ⟨.replace, "new"⟩⟩])
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
      "{\"target\":[0],\"action\":\"plusOne\"}"] do
    let json ← IO.ofExcept (Lean.Json.parse entry)
    let submission := Lean.Json.mkObj [("value", JsonProtocol.valueToJson Counters.initial),
      ("actions", Lean.Json.arr #[json])]
    check "RejectMalformedInvocation" (ComponentHistoryProtocol.verify Counters.form Counters.initial submission).toOption.isNone
  IO.println "PASS: component targets, replay, display order, and weakening"

end Tests.ComponentHistory
