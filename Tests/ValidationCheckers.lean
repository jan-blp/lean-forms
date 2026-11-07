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

end Forms.Tests.ValidationCheckers
