module

import all Std.Time.Date.Unit.Month -- for concrete date validity proofs
import all Std.Time.Date.Unit.Year

import Tests.ValidationCheckers
import Forms.Runtime.JsonProtocol
import Forms.ExampleForms.Shapes
import Forms.ExampleForms.Booking
import Forms.ExampleForms.Thermostat

-- Load executable code for `lean --run`.
meta import Tests.ValidationCheckers
meta import Forms.Runtime.JsonProtocol
meta import Forms.ExampleForms.Shapes
meta import Forms.ExampleForms.Booking
meta import Forms.ExampleForms.Thermostat

open Forms Forms.Validation Forms.ExampleForms

private def item (description : String) (quantity : Nat) : ⟦Invoice.item⟧
  | .description => description
  | .quantity => quantity
  | .unitPrice => 100

private def fixture {ty : DataType}
  (name : String)
  (checker : Checker ty)
  (values : List ⟦ty⟧)
  : Lean.Json :=
  Lean.Json.mkObj [
    ("name", Lean.toJson name),
    ("specification", Lean.Json.mkObj [("schema", ty.toJson), ("checker", checker.toJson)]),
    ("samples", Lean.toJson (values.map fun value => Lean.Json.mkObj [
      ("value", Runtime.JsonProtocol.valueToJson value),
      ("errors", Lean.toJson ((checker.run value).map ResolvedError.toJson))]))]

private def refinedFixture {ty : DataType}
  (name : String)
  (refined : RefinedDataType ty)
  (values : List ⟦ty⟧)
  : Lean.Json :=
  Lean.Json.mkObj [
    ("name", Lean.toJson name),
    ("specification", Lean.Json.mkObj [("schema", ty.toJson), ("validation", refined.toJson)]),
    ("samples", Lean.toJson (values.map fun value => Lean.Json.mkObj [
      ("value", Runtime.JsonProtocol.valueToJson value),
      ("accepted", Lean.toJson (refined.validate value).isSome),
      ("errors", Lean.toJson ((refined.errors value).map ResolvedError.toJson))]))]

private def invalid : Checker Invoice.invoice :=
  .seq (.report (.value "Index") (.locations [.item (.value 9) .self]))
    (.seq (.report (.value "Mixed") (.locations [.item (.value 0) (.field .quantity .self), .item (.value 9) .self]))
      (.seq (.report (.value "Root") (.locations [.self]))
        (.report (.value "Global") .global)))

private def hugeIndex : Checker (.list .natural) :=
  .report (.value "Huge index") (.locations [.item (.value 123456789012345678901234567890) .self])

private def sumTargets : Checker Shapes.shape :=
  .seq (.report (.value "Circle") (.locations [.constructor .circle .self]))
    (.report (.value "Rectangle") (.locations [.constructor .rectangle (.field .height .self)]))

private def nested : Checker (.list Invoice.invoice) :=
  .each (.project .self)
    (.each (.project (.field .item .self))
      (.report (.value "Nested quantity")
        (.locations [.item (.project (.field .outer (.field .index .self)))
          (.item (.project (.field .index .self)) (.field .quantity .self))])))

private def shapeCases : Checker (.list Shapes.shape) :=
  .each (.project .self)
    (.cases (.project (.field .item .self)) fun
      | .dot => .pass
      | .circle =>
        .when (.not (.natLe (.project (.field .payload .self))
          (.length (.project (.field .outer (.field .outer .self))))))
          (.report (.value "Circle")
            (.locations [.item (.project (.field .outer (.field .index .self)))
              (.constructor .circle .self)]))
      | .rectangle =>
        .when (.not (.natLe (.project (.field .payload (.field .width .self)))
          (.length (.project (.field .outer (.field .outer .self))))))
          (.report (.value "Rectangle")
            (.locations [.item (.project (.field .outer (.field .index .self)))
              (.constructor .rectangle (.field .width .self))])))

example : (shapeCases.run [⟨.circle, 2⟩]).map (·.targets) =
    [.locations [.item 0 (.constructor .circle .self)]] := by rfl
example : (shapeCases.run [⟨.rectangle, fun | .width => 2 | .height => 0⟩]).map (·.targets) =
    [.locations [.item 0 (.constructor .rectangle (.field .width .self))]] := by rfl
example : shapeCases.run [⟨.dot, by intro i; cases i⟩, ⟨.circle, 2⟩] = [] := by rfl

public def main : IO Unit := do
  let circle : ⟦Shapes.shape⟧ := { tag := .circle, payload := 0 }
  let rectangle : ⟦Shapes.shape⟧ :=
    { tag := .rectangle, payload := fun
        | .width => 2
        | .height => 0 }
  IO.println (Lean.toJson [
    refinedFixture "recursiveInvoice" Invoice.invoiceType [[], [item "A" 0, item "B" 0], [item "A" 1]],
    refinedFixture "nestedRefinements" (.list (.list Shapes.shapeType)) [[[], [circle, rectangle]]],
    refinedFixture "checkersInRefinements" (.refine Invoice.invoiceType (.ofChecker Forms.Tests.ValidationCheckers.duplicateNames))
      [[item "A" 0, item "A" 1], [item "A" 1, item "B" 1]],
    refinedFixture "invalidRefinementTargets" (.refine Invoice.invoiceType (.ofChecker invalid)) [[], [item "A" 0]],
    refinedFixture "booking" Booking.bookingType [
      Booking.draft, Booking.endDate.set { val := ⟨2027, 1, 1, by decide⟩, withinBounds := by decide } Booking.draft],
    refinedFixture "thermostat" Thermostat.thermostatType [
      Thermostat.draft, fun | .home => 4 | .away => 31],
    fixture "invoice" Forms.Tests.ValidationCheckers.checker [
      [], [item "A" 1], [item "A" 1, item "B" 2],
      [item "A" 2, item "B" 0, item "A" 0],
      [item "A" 1, item "A" 1, item "A" 1],
      [item "ä" 1, item "a" 1, item "ä" 1],
      [item "Huge" 123456789012345678901234567890]],
    fixture "branching" (ty := .natural)
      (.ite (.natLe (.project .self) (.value 5))
        (.report (.value "At most five") .global)
        (.report (.value "Above five") .global)) [0, 5, 6],
    fixture "pass" (ty := Invoice.invoice) .pass [[], [item "A" 0]],
    fixture "passThenReport" (ty := Invoice.invoice)
      (.seq .pass (.report (.value "Error") .global)) [[]],
    fixture "reportThenPass" (ty := Invoice.invoice)
      (.seq (.report (.value "Error") .global) .pass) [[]],
    fixture "invalidTargets" invalid [[item "A" 1], []],
    fixture "hugeIndex" hugeIndex [[], [1]],
    fixture "shapeCases" shapeCases [[], [circle], [rectangle],
      [⟨.circle, 3⟩, rectangle], [⟨.dot, by intro i; cases i⟩, ⟨.circle, 2⟩]],
    fixture "sumTargets" sumTargets [circle, rectangle],
    fixture "nested" nested [[[], [item "A" 1, item "B" 0]]]]).compress
