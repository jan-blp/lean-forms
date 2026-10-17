import Forms.Core.Component.Builder

namespace Forms.ExampleForms.Shapes
open Composition

inductive Shape where
  | dot | circle | rectangle
  deriving DecidableEq, Repr

instance : FinEnum Shape :=
  FinEnum.ofList [.dot, .circle, .rectangle] (by grind [Shape])

def shapeTags : Enum where
  type := Shape
  label
    | .dot => "dot"
    | .circle => "circle"
    | .rectangle => "rectangle"

inductive RectangleField where
  | width | height
  deriving DecidableEq, Repr

instance : FinEnum RectangleField :=
  FinEnum.ofList [.width, .height] (by grind [RectangleField])

def rectangleFields : Enum where
  type := RectangleField
  label
    | .width => "width"
    | .height => "height"

def noFields : Enum where
  type := Empty
  label := Empty.elim
  label_injective := by intro i; exact Empty.elim i

abbrev rectangle : DataType := .record rectangleFields (fun _ => .natural)
abbrev constructors : shapeTags → DataType
  | .dot => .record noFields Empty.elim
  | .circle => .natural
  | .rectangle => rectangle

abbrev shape : DataType := .sum shapeTags constructors

def initial : ⟦shape⟧ := ⟨.circle, 3⟩

def form : Component shape :=
  (show Component.Builder shape shape from
    Component.Builder.sum "Shape"
      (fun
        | .dot => Component.Builder.group "Dot" (fun i => nomatch i)
        | .circle => Component.Builder.field "Radius" .naturalInput
        | .rectangle => Component.Builder.group "Dimensions" fun
          | .width => Component.Builder.field "Width" .naturalInput
          | .height => Component.Builder.field "Height" .naturalInput)
      (fun
        | .dot => fun i => nomatch i
        | .circle => 3
        | .rectangle => fun | .width => 4 | .height => 2)) .self

end Forms.ExampleForms.Shapes
