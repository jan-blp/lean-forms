module

public import Forms.Runtime.CheckerProtocol
public import Tests.ValidationCheckers
public import Forms.ExampleForms.Shapes

@[expose] public section

namespace Tests.CheckerProtocol
open Forms Forms.Validation Forms.Runtime Forms.ExampleForms

def roundTrip {type : DataType} (checker : Checker type) (value : ⟦type⟧) : IO Unit := do
  let actual ← IO.ofExcept (CheckerProtocol.evaluate type.toJson checker.toJson (JsonProtocol.valueToJson value))
  let expected := Lean.toJson ((checker.run value).map ResolvedError.toJson)
  unless actual == expected do
    throw (IO.userError s!"Checker round trip: expected {expected.compress}, got {actual.compress}")

def run : IO Unit := do
  let item (name : String) (quantity : Nat) : ⟦Invoice.item⟧ := fun
    | .description => name
    | .quantity => quantity
    | .unitPrice => 100
  for value in [[], [item "A" 0, item "A" 1], [item "🌍\x00" 0, item "🌍\x00" 0]] do
    roundTrip Forms.Tests.ValidationCheckers.checker value
    roundTrip (.pass : Checker Invoice.invoice) value
  let invalid : Checker (.list .natural) := .seq
    (.report (.value "invalid") (.locations [.item (.value (2 ^ 256)) .self]))
    (.report (.value "global") .global)
  roundTrip invalid []
  roundTrip invalid [1, 2]
  let branch : Checker Shapes.shape := .seq
    (.report (.value "circle") (.locations [.constructor .circle .self]))
    (.report (.value "rectangle") (.locations [.constructor .rectangle (.field .height .self)]))
  roundTrip branch { tag := .circle, payload := 0 }
  roundTrip branch { tag := .rectangle, payload := fun | .width => 1 | .height => 0 }
  let active : Checker Shapes.shape := .cases (.project .self) fun
    | .dot => .pass
    | .circle => .ite (.natLe (.project (.field .payload .self)) (.value 10))
        .pass (.report (.value "large circle") (.locations [.constructor .circle .self]))
    | .rectangle => .report
        (.natToText (.project (.field .payload (.field .width .self))))
        (.locations [.constructor .rectangle (.field .width .self)])
  roundTrip active { tag := .circle, payload := 5 }
  roundTrip active { tag := .circle, payload := 20 }
  roundTrip active { tag := .rectangle, payload := fun | .width => 12 | .height => 2 }
  IO.println "PASS: decoded checker execution matches core Lean checkers"

end Tests.CheckerProtocol
