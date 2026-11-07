module

import all Std.Time.Date.Unit.Month -- for concrete date validity proofs
import all Std.Time.Date.Unit.Year

public import Forms.ExampleForms.Counters
public import Forms.Runtime.CompiledView
public import Forms.Runtime.ComponentHistoryProtocol

@[expose] public section

namespace Tests.FieldHistory
open Forms Forms.Composition Forms.Runtime Forms.ExampleForms

def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

def checkWidget {ty : DataType}
  (widget : Widget ty)
  (initial argument : ⟦ty⟧)
  : IO Unit := do
  let component := Component.field Path.self "Value" widget
  let history ← IO.ofExcept (ComponentHistory.replay component initial
    #[⟨.replace, argument⟩, ⟨.replace, argument⟩])
  let encoded := ComponentHistoryProtocol.encode history
  let checked ← IO.ofExcept (ComponentHistoryProtocol.verify component initial encoded)
  check "FieldReplacementRoundTrip" (JsonProtocol.valueToJson checked.value == JsonProtocol.valueToJson argument)
  check "RepeatedFieldReplacements" (checked.actions.size == 2)
  let entries ← IO.ofExcept (encoded.getObjVal? "actions")
  check "FieldReplacementWireFormat" (entries == Lean.Json.arr (Array.replicate 2
    (Lean.Json.mkObj [("target", Lean.toJson ([] : List String)),
      ("action", Lean.toJson "replace"), ("argument", JsonProtocol.valueToJson argument)])))

def mixed : Component Counters.state :=
  .stack (items := Counters.sides) none (fun
    | .left => Counters.widget .left
    | .right => .field (.field .right .self) "Right" .naturalInput)

def visibleField : Component .natural :=
  .visibleWhen (.natLe (.project .self) (.value 0))
    (.field .self "Value" .naturalInput)

def hideField : visibleField.ValidInvocation 0 :=
  ⟨⟨.replace, (1 : Nat)⟩, by
    change decide (0 ≤ 0) = true
    decide⟩

example : visibleField.applyValidInvocation 0 hideField = 1 := rfl

example (invocation : visibleField.ValidInvocation 1) : False := by
  have visible := invocation.property
  change decide (1 ≤ 0) = true at visible
  contradiction

def disabledField : Component .natural :=
  .disabledWhen (.natLe (.value 1) (.project .self))
    (.field .self "Value" .naturalInput)

example (invocation : disabledField.ValidInvocation 1) : False := by
  have enabled := invocation.property
  change decide (1 ≤ 1) = false at enabled
  contradiction

def testValidatedInvocation : IO Unit := do
  let validated ← IO.ofExcept (visibleField.validateInvocation 0 ⟨.replace, (1 : Nat)⟩)
  let current := visibleField.applyValidInvocation 0 validated
  let disabled := Component.disabledWhen (.value true) visibleField
  check "OuterConditionCheckedBeforeInnerCondition"
    (match disabled.validateInvocation current ⟨.replace, (0 : Nat)⟩ with
      | .error error => error == .disabled
      | .ok _ => false)

def run : IO Unit := do
  testValidatedInvocation
  checkWidget .textInput "old" "new"
  checkWidget .naturalInput 0 123456789012345678901234567890
  checkWidget .checkbox false true
  checkWidget (.select (domain := Counters.sides)) .left .right
  checkWidget .dateInput
    ⟨⟨2028, 2, 28, by decide⟩, by decide⟩
    ⟨⟨2028, 2, 29, by decide⟩, by decide⟩
  let history ← IO.ofExcept (ComponentHistory.replay mixed Counters.initial
    #[⟨.left, ⟨.plusOne, ()⟩⟩, ⟨.right, ⟨.replace, (42 : Nat)⟩⟩])
  check "MixedFieldAndWidgetHistory" (history.value .left == 1 && history.value .right == 42)
  let encoded := ComponentHistoryProtocol.encode history
  let _ ← IO.ofExcept (ComponentHistoryProtocol.verify mixed Counters.initial encoded)
  let field := Component.field Path.self "Value" Widget.naturalInput
  for entry in [
      "{\"target\":[],\"action\":\"other\",\"argument\":\"1\"}",
      "{\"target\":[],\"action\":\"replace\"}",
      "{\"target\":[],\"action\":\"replace\",\"argument\":true}",
      "{\"target\":[\"extra\"],\"action\":\"replace\",\"argument\":\"1\"}",
      "{\"target\":[],\"action\":\"replace\",\"argument\":\"1\",\"extra\":true}"] do
    let entry ← IO.ofExcept (Lean.Json.parse entry)
    check "RejectMalformedFieldInvocation" (ComponentHistoryProtocol.verify field 0
      (Lean.Json.mkObj [("value", Lean.toJson "1"), ("actions", Lean.Json.arr #[entry])])).toOption.isNone
  IO.println "PASS: field replacement history, targets, conditions, and decoding"

end Tests.FieldHistory
