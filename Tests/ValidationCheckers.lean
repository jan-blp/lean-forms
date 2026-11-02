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

end Forms.Tests.ValidationCheckers
