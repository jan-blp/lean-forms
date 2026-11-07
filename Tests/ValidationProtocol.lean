module

public import Forms.Runtime.ValidationProtocol
public import Forms.ExampleForms.Shapes
public import Forms.ExampleForms.Invoice

@[expose] public section

namespace Tests.ValidationProtocol
open Forms Forms.Validation Forms.Runtime Forms.ExampleForms

def roundTrip {type : DataType} (refined : RefinedDataType type) (value : ⟦type⟧) : IO Unit := do
  let actual ← IO.ofExcept (ValidationProtocol.evaluate type.toJson refined.toJson
    (JsonProtocol.valueToJson value))
  let expected := Lean.toJson ((refined.errors value).map ResolvedError.toJson)
  unless actual == expected do
    throw (IO.userError s!"Refinement round trip: expected {expected.compress}, got {actual.compress}")

def run : IO Unit := do
  let circle : ⟦Shapes.shape⟧ := { tag := .circle, payload := 0 }
  let rectangle : ⟦Shapes.shape⟧ :=
    { tag := .rectangle, payload := fun | .width => 0 | .height => 0 }
  roundTrip (.list (.list Shapes.shapeType)) [[], [circle, rectangle]]
  roundTrip Invoice.invoiceType []
  roundTrip Invoice.invoiceType [fun | .description => "A" | .quantity => 0 | .unitPrice => 0]
  let checked : RefinedDataType (.list .natural) := .refine (.base _) (.ofChecker
    (.seq (.report (.value "invalid 🌍\x00") (.locations [.item (.value (2 ^ 256)) .self]))
      (.seq (.report (.value "self") (.locations [.self])) (.report (.value "global") .global))))
  roundTrip (.list checked) [[], [1]]
  roundTrip (.refine checked (.ofChecker (.report (.value "outer") .global))) []
  IO.println "PASS: decoded recursive validation matches core Lean refinements"

end Tests.ValidationProtocol
