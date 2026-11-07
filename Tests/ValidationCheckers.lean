module

public import Forms.Core.Validation
public import Forms.ExampleForms.Invoice

@[expose] public section

namespace Forms.Tests.ValidationCheckers

open Validation ExampleForms.Invoice

def quantities : Checker invoice := fun values =>
  (List.finRange values.length).flatMap fun index =>
    if 1 ≤ values[index] .quantity then [] else
      [{ message := "Quantity must be at least 1.", targets := .locations [.item index (.field .quantity .self)] }]

def duplicateNames : Checker invoice := fun values =>
  (List.finRange values.length).flatMap fun first =>
    (List.finRange values.length).flatMap fun second =>
      if first.val < second.val && values[first] .description == values[second] .description then
        [{ message := "Duplicate item: " ++ values[first] .description,
           targets := .locations [.item first (.field .description .self), .item second (.field .description .self)] }]
      else []

def checker : Checker invoice := fun value => quantities value ++ duplicateNames value

-- `all` binds the enclosing value, current item, and zero-based index.
def boundedItems : Expr (.list .natural) .boolean :=
  .all (.project .self)
    (.and
      (.natLe (.project (.field .item .self))
        (.length (.project (.field .outer .self))))
      (.natLe (.project (.field .index .self))
        (.project (.field .item .self))))

example : boundedItems.eval [2, 2] = true := by rfl
example : boundedItems.eval [3] = false := by rfl
example : boundedItems.eval [0, 0] = false := by rfl
example : boundedItems.eval [] = true := by rfl

-- Weakening must retain the original outer value inside the predicate.
def embeddedItems : Expr (IterationContext .natural (.list .natural)) .boolean :=
  boundedItems.weaken (.field .item .self)

example : embeddedItems.eval (fun | .outer => 0 | .item => [2, 2] | .index => 99) = true := by rfl
example : embeddedItems.eval (fun | .outer => 99 | .item => [3] | .index => 0) = false := by rfl

def nestedAll : Expr (.list .natural) .boolean :=
  .all (.project .self)
    (.all (outer := IterationContext (.list .natural) .natural)
      (.project (.field .outer .self))
      (.natLe (.project (.field .item .self))
        (.project (.field .outer (.field .item .self)))))

example : nestedAll.eval [2, 2] = true := by rfl
example : nestedAll.eval [1, 2] = false := by rfl

end Forms.Tests.ValidationCheckers
