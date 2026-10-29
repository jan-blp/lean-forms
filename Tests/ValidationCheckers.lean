import Forms.Core.Validation
import Forms.ExampleForms.Invoice

namespace Forms.Tests.ValidationCheckers

open Validation ExampleForms.Invoice

abbrev ItemInput := IterationContext invoice item
abbrev PairInput := IterationContext ItemInput item

def quantities : Checker invoice :=
  .each (.project .self)
    (.when (.not (.natLe (.value 1) (.project (.field .item (.field .quantity .self)))))
      (.report (.value "Quantity must be at least 1.")
        (.locations [.item (.project (.field .index .self)) (.field .quantity .self)])))

private def firstIndex : Expr PairInput .natural :=
  .project (.field .outer (.field .index .self))

private def secondIndex : Expr PairInput .natural :=
  .project (.field .index .self)

private def firstName : Expr PairInput .text :=
  .project (.field .outer (.field .item (.field .description .self)))

private def secondName : Expr PairInput .text :=
  .project (.field .item (.field .description .self))

def duplicateNames : Checker invoice :=
  .each (.project .self)
    (.each (.project (.field .outer .self))
      (.when (.and (.not (.natLe secondIndex firstIndex)) (.textEq firstName secondName))
        (.report (.textAppend (.value "Duplicate item: ") firstName)
          (.locations [
            .item firstIndex (.field .description .self),
            .item secondIndex (.field .description .self)]))))

def checker : Checker invoice := .seq quantities duplicateNames

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
