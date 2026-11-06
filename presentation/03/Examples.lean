import Forms.Core.RefinedDataType
import Forms.ExampleForms.Thermostat
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Shapes

namespace Forms.Presentation.Refinements
open Validation

-- Expression examples. The Boolean refinement model is in OldRefinements.lean.
def isPositive : Expr .natural .boolean :=
  .natLe (.value 1) (.project .self)

def inRange : Expr .natural .boolean :=
  .and isPositive (.natLe (.project .self) (.value 10))

def allPositive : Expr (.list .natural) .boolean :=
  .all (.project .self) (isPositive.weaken (.field .item .self))

open ExampleForms.Thermostat in
def awayNotWarmer : Expr thermostat .boolean :=
  .natLe (.project awayTemperature) (.project homeTemperature)

open ExampleForms.Thermostat in
def homeInRange : Expr thermostat .boolean :=
  .and (.natLe (.value 5) (.project homeTemperature))
       (.natLe (.project homeTemperature) (.value 30))

open ExampleForms.Thermostat in
def awayInRange : Expr thermostat .boolean :=
  .and (.natLe (.value 5) (.project awayTemperature))
       (.natLe (.project awayTemperature) (.value 30))

#guard homeInRange.eval (fun _ => 5) == true
#guard homeInRange.eval (fun _ => 4) == false
#guard awayInRange.eval (fun _ => 30) == true
#guard awayInRange.eval (fun _ => 31) == false

#guard isPositive.eval 0 == false
#guard isPositive.eval 3 == true
#guard inRange.eval 0 == false
#guard inRange.eval 3 == true
#guard inRange.eval 12 == false
#guard allPositive.eval [2, 1, 4] == true
#guard allPositive.eval [2, 0, 4] == false
#guard allPositive.eval [0, 0, 4] == false
#guard allPositive.eval [] == true
#guard awayNotWarmer.eval (ExampleForms.Thermostat.thermostatType.erase ExampleForms.Thermostat.initial) == true

example (n : Nat) : isPositive.eval n = true ↔ 0 < n := by
  grind [isPositive, Expr.eval, Path.get]

-- Part 2: preserve explanations, then connect acceptance to a proposition.
-- A checked property connects an executable check to a Lean proposition.
def positiveProperty : CheckedProperty .natural :=
  .require (fun n => 0 < n)
    (.natLe (.value 1) (.project .self))
    (.value "Quantity must be at least 1.")
    (.locations [.self])

def positive : RefinedDataType .natural :=
  .refine (.base .natural) positiveProperty

def three : positive.ValidatedValue := ⟨3, by change 0 < (3 : Nat); decide⟩
#guard three.val == 3
#guard (positive.validate 0).isNone
#guard (positive.validate 3).isSome
#guard (positive.errors 0).map (·.message) == ["Quantity must be at least 1."]
#guard (positive.errors 3).isEmpty

-- The checker can also be assembled directly.
def quantityChecker : Checker .natural :=
  .when (.not (.natLe (.value 1) (.project .self)))
    (.report (.value "Quantity must be at least 1.")
      (.locations [.self]))

#guard (quantityChecker.run 0).length == 1
#guard (quantityChecker.run 3).isEmpty

-- A separate check can contribute another diagnostic.
def atMostTen : Checker .natural :=
  .when (.not (.natLe (.project .self) (.value 10)))
    (.report (.value "Quantity must be at most 10.") (.locations [.self]))

def quantityChecks : Checker .natural := .seq quantityChecker atMostTen
#guard (quantityChecks.run 0).map (·.message) == ["Quantity must be at least 1."]
#guard (quantityChecks.run 3).isEmpty
#guard (quantityChecks.run 12).map (·.message) == ["Quantity must be at most 10."]

-- Structural refinement reuses the same rule at every list position.
def quantities : RefinedDataType (.list .natural) := .list positive
#guard (quantities.validate [2, 0, 4]).isNone
#guard (quantities.validate [2, 1, 4]).isSome
#guard (quantities.errors [2, 0, 4]).length == 1


-- An each checker carries both the element and its index.
def eachQuantity : Checker (.list .natural) :=
  .each (.project .self)
    (.when (.not (.natLe (.value 1) (.project (.field .item .self))))
      (.report (.value "Quantity must be at least 1.")
        (.locations [.item (.project (.field .index .self)) .self])))
#guard (eachQuantity.run [2, 0, 4]).length == 1
#guard (eachQuantity.run [2, 1, 4]).isEmpty

-- Thermostat demo: each temperature is in range, but away exceeds home.
open ExampleForms.Thermostat in
def tooWarmAway : ⟦thermostat⟧ := fun
  | .home => 18
  | .away => 22

open ExampleForms.Thermostat in
def correctedTemperatures : ⟦thermostat⟧ := fun
  | .home => 18
  | .away => 16

open ExampleForms.Thermostat in
def equalTemperatures : ⟦thermostat⟧ := fun _ => 22

#guard awayNotWarmer.eval tooWarmAway == false
#guard awayNotWarmer.eval correctedTemperatures == true
#guard awayNotWarmer.eval equalTemperatures == true
#guard (ExampleForms.Thermostat.thermostatType.validate tooWarmAway).isNone
#guard (ExampleForms.Thermostat.thermostatType.errors tooWarmAway).map (·.message) ==
  ["Away temperature must not exceed home temperature."]
#guard (ExampleForms.Thermostat.thermostatType.validate correctedTemperatures).isSome
#guard (ExampleForms.Thermostat.thermostatType.validate equalTemperatures).isSome

-- Local and record-wide checks use different input types.
def temperatureInRange : Expr .natural .boolean :=
  .and (.natLe (.value 5) (.project .self))
       (.natLe (.project .self) (.value 30))

open ExampleForms.Thermostat in
def thermostatChecker : Checker thermostat :=
  .when (.not awayNotWarmer)
    (.report
      (.value "Away temperature must not exceed home temperature.")
      (.locations [awayTemperature.locationExpr]))

#guard temperatureInRange.eval 4 == false
#guard temperatureInRange.eval 5 == true
#guard temperatureInRange.eval 30 == true
#guard temperatureInRange.eval 35 == false
#guard (thermostatChecker.run tooWarmAway).length == 1
#guard (thermostatChecker.run correctedTemperatures).isEmpty

-- Invoice demo: local rules lift to their item and field locations.
open ExampleForms.Invoice in
def invalidInvoice : ⟦invoice⟧ := [fun
  | .description => "Notebook"
  | .quantity => 0
  | .unitPrice => 0]
#guard (ExampleForms.Invoice.invoiceType.errors invalidInvoice).length == 2
#guard (ExampleForms.Invoice.invoiceType.validate invalidInvoice).isNone

-- A checker-defined property has soundness by construction.
def acceptedQuantity : CheckedProperty .natural :=
  .ofChecker quantityChecks

example (n : Nat) (h : (positiveProperty.checker.run n).isEmpty = true) : 0 < n :=
  positiveProperty.sound n h

-- Checker-design slides: contextual rules with list and sum error targets.
namespace CheckerDesign

open ExampleForms.Shapes (rectangle rectangleFields RectangleField)

inductive ShapeTag where
  | circle | rectangle
  deriving DecidableEq

instance : FinEnum ShapeTag :=
  FinEnum.ofList [.circle, .rectangle] (by grind [ShapeTag])

def shapeTags : Enum where
  type := ShapeTag
  label | .circle => "circle" | .rectangle => "rectangle"

abbrev shape : DataType := .sum shapeTags fun
  | .circle => .natural
  | .rectangle => rectangle

inductive DrawingField where
  | side | shapes
  deriving DecidableEq

instance : FinEnum DrawingField :=
  FinEnum.ofList [.side, .shapes] (by grind [DrawingField])

def drawingFields : Enum where
  type := DrawingField
  label
    | .side => "side"
    | .shapes => "shapes"

abbrev drawing : DataType := .record drawingFields fun
  | .side => .natural
  | .shapes => .list shape

def widthsFit : Expr drawing .boolean :=
  .all (.project (.field .shapes .self))
    (.natLe
      (.cases (.project (.field .item .self)) fun
        | .circle => .natMul (.value 2) (.project .self)
        | .rectangle => .project (.field .width .self))
      (.project (.field .outer (.field DrawingField.side .self))))

def widthChecker : Checker drawing :=
  .each (.project (.field .shapes .self))
    (.cases (.project (.field .item .self)) fun
      | .circle =>
        .when (.not (.natLe
          (.natMul (.value 2) (.project (.field .payload .self)))
          (.project (.field .outer (.field .outer (.field .side .self))))))
          (.report (.value "Circle is wider than the canvas.")
            (.locations [.field .shapes
              (.item (.project (.field .outer (.field .index .self)))
                (.constructor .circle .self))]))
      | .rectangle =>
        .when (.not (.natLe
          (.project (.field .payload (.field .width .self)))
          (.project (.field .outer (.field .outer (.field .side .self))))))
          (.report (.value "Rectangle is wider than the canvas.")
            (.locations [.field .shapes
              (.item (.project (.field .outer (.field .index .self)))
                (.constructor .rectangle (.field .width .self)))])))

def drawingExample : ⟦drawing⟧ := fun
  | .side => 100
  | .shapes => [⟨.circle, 20⟩,
      ⟨.rectangle, fun | .width => 120 | .height => 40⟩]

#guard !widthsFit.eval drawingExample
#guard widthsFit.eval (fun
  | .side => 100
  | .shapes => [⟨.circle, 50⟩])
#guard !widthsFit.eval (fun
  | .side => 100
  | .shapes => [⟨.circle, 51⟩])

def multipleFailures : ⟦drawing⟧ := fun
  | .side => 100
  | .shapes => [⟨.rectangle, fun | .width => 120 | .height => 40⟩,
      ⟨.circle, 20⟩,
      ⟨.rectangle, fun | .width => 150 | .height => 30⟩]

#guard (widthChecker.run drawingExample).length == 1
#guard (widthChecker.run multipleFailures).length == 2

-- The same list index selects the active rectangle payload and its width field.
example : (widthChecker.run drawingExample).map (·.targets) =
    [.locations [.field .shapes (.item 1 (.constructor .rectangle (.field .width .self)))]] := by rfl
example : (widthChecker.run multipleFailures).map (·.targets) =
    [.locations [.field .shapes (.item 0 (.constructor .rectangle (.field .width .self)))],
     .locations [.field .shapes (.item 2 (.constructor .rectangle (.field .width .self)))]] := by rfl

-- Equal widths pass; oversized circles target their radius.
#guard (widthChecker.run (fun
  | .side => 100
  | .shapes => [⟨.rectangle, fun | .width => 100 | .height => 40⟩])).isEmpty
example : (widthChecker.run (fun
  | .side => 0
  | .shapes => [⟨.circle, 20⟩])).map (·.targets) =
    [.locations [.field .shapes (.item 0 (.constructor .circle .self))]] := by rfl
#guard (widthChecker.run (fun
  | .side => 100
  | .shapes => [⟨.circle, 50⟩])).isEmpty

def WidthsFit (value : ⟦drawing⟧) : Prop :=
  ∀ s ∈ value .shapes, match s with
    | ⟨.circle, radius⟩ => 2 * radius ≤ value .side
    | ⟨.rectangle, sides⟩ => sides .width ≤ value .side

theorem widthChecker_sound (value : ⟦drawing⟧)
    (h : (widthChecker.run value).isEmpty = true) : WidthsFit value := by
  rw [WidthsFit, ← List.zipIdx_map_fst 0 (value .shapes), List.forall_mem_map]
  rintro ⟨⟨tag, _⟩, _⟩ hs
  have accepted := List.flatMap_eq_nil_iff.mp (List.isEmpty_iff.mp h) _ hs
  cases tag <;>
    simp [ScopedChecker.eval, ScopedChecker.when, Expr.eval, Path.get] at accepted <;> grind

def widthsFitProperty : CheckedProperty drawing where
  property := WidthsFit
  checker := widthChecker
  sound := widthChecker_sound

def atLeastFive : Expr .natural .boolean :=
  .natLe (.value 5) (.project .self)

def atLeastFiveType : RefinedDataType .natural :=
  .refine (.base .natural)
    (.require (fun n => 5 ≤ n) atLeastFive
      (.value "Must be at least 5.") (.locations [.self])
      (by intro n; grind [atLeastFive, Expr.eval, Path.get]))

#guard (atLeastFiveType.validate 4).isNone
#guard (atLeastFiveType.validate 5).isSome
example (value : atLeastFiveType.ValidatedValue) : 5 ≤ value.val := value.property

end CheckerDesign

end Forms.Presentation.Refinements
