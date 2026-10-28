import Forms.ExampleForms.Shapes

namespace Forms.Presentation.Sums

open Composition
open Forms.ExampleForms.Shapes (rectangleFields)

inductive ShapeTag where
  | dot
  | circle
  | rectangle
  deriving DecidableEq, Repr

instance : FinEnum ShapeTag :=
  FinEnum.ofList [.dot, .circle, .rectangle] (by grind [ShapeTag])

def shapeTags : Enum where
  type := ShapeTag
  label
    | .dot => "dot"
    | .circle => "circle"
    | .rectangle => "rectangle"

def noFields : Enum where
  type := Empty
  label := Empty.elim
  label_injective := by intro i; exact Empty.elim i

abbrev unit : DataType := .record noFields Empty.elim

def unitValue : ⟦unit⟧ := fun i => nomatch i

abbrev rectangle : DataType := .record rectangleFields fun
  | .width => .natural
  | .height => .natural

abbrev constructors : shapeTags → DataType
  | .dot => unit
  | .circle => .natural
  | .rectangle => rectangle

abbrev shape : DataType := .sum shapeTags constructors

def initial : ⟦shape⟧ := ⟨.circle, 3⟩

def form : Component shape :=
  .sum .self "Shape"
    (branches := fun
      | .dot => .stack none (items := noFields) (children := fun i => nomatch i)
      | .circle => .field .self "Radius" .naturalInput
      | .rectangle => .stack none (items := rectangleFields) (children := fun
          | .width => .field (.field .width .self) "Width" .naturalInput
          | .height => .field (.field .height .self) "Height" .naturalInput))
    (defaults := fun
      | .dot => fun i => nomatch i
      | .circle => 3
      | .rectangle => fun
        | .width => 4
        | .height => 2)

example : True := by
  fail_if_success have : ⟦shape⟧ := ⟨.circle, "three"⟩
  trivial

#guard initial.tag == .circle
example : initial.payload = (3 : Nat) := rfl

end Forms.Presentation.Sums
