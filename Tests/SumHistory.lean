module

public import Forms.ExampleForms.Shapes
public import Forms.Runtime.Tui
public import Tests.Weakening

@[expose] public section

namespace Tests.SumHistory
open Forms Forms.Composition Forms.Runtime Forms.ExampleForms

def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

def actions : Array Shapes.form.Invocation := #[
  .inPayload .circle ⟨.replace, (8 : Nat)⟩,
  .select .circle,
  .select .rectangle,
  .inPayload .rectangle ⟨.width, ⟨.replace, (9 : Nat)⟩⟩,
  .select .circle]

example : Shapes.form.applyValidInvocation Shapes.draft (.inPayload ⟨.replace, (8 : Nat)⟩) =
    (⟨.circle, 8⟩ : ⟦Shapes.shape⟧) := rfl

def nested : Component (.sum Shapes.shapeTags fun _ => Shapes.shape) :=
  .sum .self "Nested" (fun _ => Shapes.form) (fun _ => Shapes.draft)

def testNested : IO Unit := do
  let initial : ⟦.sum Shapes.shapeTags fun _ => Shapes.shape⟧ := ⟨.circle, Shapes.draft⟩
  let history ← IO.ofExcept (ComponentHistory.replay nested initial #[
    .inPayload .circle (.select .rectangle),
    .inPayload .circle (.inPayload .rectangle ⟨.width, ⟨.replace, (9 : Nat)⟩⟩)])
  let encoded := ComponentHistoryProtocol.encode history
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify nested initial encoded)
  let entries ← IO.ofExcept (encoded.getObjVal? "actions" >>= Lean.Json.getArr?)
  let target ← IO.ofExcept (entries[1]!.getObjVal? "target")
  check "NestedSumTarget" (target == Lean.toJson (["circle", "rectangle", "width"] : List String))
  let reset ← IO.ofExcept (ComponentHistory.replay nested history.value #[.select .dot, .select .circle])
  check "OuterSwitchResetsNestedPayload" (JsonProtocol.valueToJson reset.value == JsonProtocol.valueToJson initial)

def expectError {ty : DataType}
  (component : Component ty)
  (current : ⟦ty⟧)
  (invocation : component.Invocation)
  (expected : Component.InvocationError)
  : IO Unit :=
  check "RejectInvalidSumInvocation" (match component.applyInvocation current invocation with
    | .error error => error == expected
    | .ok _ => false)

def run : IO Unit := do
  testNested
  let history ← IO.ofExcept (ComponentHistory.replay Shapes.form Shapes.draft actions)
  check "ReturningToConstructorUsesDefault"
    (JsonProtocol.valueToJson history.value == JsonProtocol.valueToJson Shapes.draft)
  let unchanged ← IO.ofExcept (ComponentHistory.replay Shapes.form Shapes.draft actions[:2].toArray)
  check "SelectingActiveConstructorPreservesEdits"
    (JsonProtocol.valueToJson unchanged.value == Lean.Json.mkObj [("tag", Lean.toJson "circle"), ("value", Lean.toJson "8")])
  let encoded := ComponentHistoryProtocol.encode history
  let expected ← IO.ofExcept (Lean.Json.parse
    "{\"value\":{\"tag\":\"circle\",\"value\":\"3\"},\"actions\":[{\"target\":[\"circle\"],\"action\":\"replace\",\"argument\":\"8\"},{\"target\":[],\"action\":\"select\",\"constructor\":\"circle\"},{\"target\":[],\"action\":\"select\",\"constructor\":\"rectangle\"},{\"target\":[\"rectangle\",\"width\"],\"action\":\"replace\",\"argument\":\"9\"},{\"target\":[],\"action\":\"select\",\"constructor\":\"circle\"}]}")
  check "SumWireFormat" (encoded == expected)
  let checked ← IO.ofExcept (ComponentHistoryProtocol.verify Shapes.form Shapes.draft encoded)
  check "SumHistoryRoundTrip" (ComponentHistoryProtocol.encode checked == encoded)
  expectError Shapes.form Shapes.draft (.inPayload .rectangle ⟨.width, ⟨.replace, (7 : Nat)⟩⟩) .inactiveConstructor
  let dot ← IO.ofExcept (Shapes.form.applyInvocation Shapes.draft (.select .dot))
  expectError Shapes.form dot (.inPayload .circle ⟨.replace, (7 : Nat)⟩) .inactiveConstructor
  let hidden := Component.visibleWhen (.value false) Shapes.form
  let disabled := Component.disabledWhen (.value true) Shapes.form
  for invocation in actions do
    expectError hidden Shapes.draft invocation .hidden
    expectError disabled Shapes.draft invocation .disabled
  let hiddenBranch : Component Shapes.shape :=
    .sum .self "Shape" (fun tag => .visibleWhen (.value false)
      (match tag with
        | .dot => .text (.value "Dot")
        | .circle => .field .self "Radius" .naturalInput
        | .rectangle => .text (.value "Rectangle")))
      (fun tag => match tag with
        | .dot => fun i => nomatch i
        | .circle => 3
        | .rectangle => fun _ => 2)
  let selected ← IO.ofExcept (hiddenBranch.applyInvocation dot (.select .circle))
  expectError hiddenBranch selected (.inPayload .circle ⟨.replace, (7 : Nat)⟩) .hidden
  let shapes := Component.list Path.self "Shapes" Shapes.form Shapes.draft
  let listed ← IO.ofExcept (ComponentHistory.replay shapes [] #[
    .appendDefault, .appendDefault, .item 1 (.select .rectangle), .remove 0,
    .item 0 (.inPayload .rectangle ⟨.height, ⟨.replace, (6 : Nat)⟩⟩)])
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify shapes [] (ComponentHistoryProtocol.encode listed))
  let weakened := Shapes.form.weaken (Tests.Weakening.contentPath Shapes.shape)
  let initial := Tests.Weakening.wrap Shapes.draft
  let wrapped ← IO.ofExcept (ComponentHistory.replay weakened initial actions)
  check "SumWeakeningPreservesSibling" (wrapped.value .title == "Keep this title")
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify weakened initial (ComponentHistoryProtocol.encode wrapped))
  for entry in [
      "{\"target\":[],\"action\":\"select\"}",
      "{\"target\":[],\"action\":\"select\",\"constructor\":\"missing\"}",
      "{\"target\":[],\"action\":\"select\",\"constructor\":0}",
      "{\"target\":[],\"action\":\"select\",\"constructor\":\"circle\",\"argument\":\"9\"}",
      "{\"target\":[\"missing\"],\"action\":\"replace\",\"argument\":\"9\"}",
      "{\"target\":[0],\"action\":\"replace\",\"argument\":\"9\"}",
      "{\"target\":[\"circle\"],\"action\":\"replace\",\"argument\":false}",
      "{\"target\":[\"rectangle\",\"width\"],\"action\":\"replace\",\"argument\":\"9\"}"] do
    let entry ← IO.ofExcept (Lean.Json.parse entry)
    check "RejectMalformedOrInactiveSumAction" (ComponentHistoryProtocol.verify Shapes.form Shapes.draft
      (Lean.Json.mkObj [("value", JsonProtocol.valueToJson Shapes.draft), ("actions", Lean.Json.arr #[entry])])).toOption.isNone
  IO.println "PASS: sum history, defaults, active payloads, targets, and decoding"

end Tests.SumHistory
