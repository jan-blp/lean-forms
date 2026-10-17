import Forms.Core.Form
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Shapes

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
abbrev constructors : shapeTags.type → DataType
  | .dot => .record noFields Empty.elim
  | .circle => .natural
  | .rectangle => rectangle

abbrev shape : DataType := .sum shapeTags constructors

def size : RefinedDataType .natural :=
  let minimum : Nat := 1
  .refine (.base .natural)
    { condition := .natLe (.value minimum) (.project .self)
      errorMessage := s!"Size must be at least {minimum}."
      errorLocation := some ⟨.self⟩ }

def shapeType : RefinedDataType shape :=
  .sum fun
    | .dot => .record (fun i => nomatch i)
    | .circle => size
    | .rectangle => .record (fun _ => size)

def initial : RefinedDataType.ValidatedValue shapeType := ⟨.circle, ⟨(3 : Nat), by decide⟩⟩
def draft : DataType.denote shape := RefinedDataType.erase shapeType initial

def form : Form shape shape :=
  .sum "Shape"
    (fun
      | .dot => .group "Dot" (fun i => nomatch i)
      | .circle => .field "Radius" .naturalInput
      | .rectangle => .group "Dimensions" fun
        | .width => .field "Width" .naturalInput
        | .height => .field "Height" .naturalInput)
    (fun
      | .dot => fun i => nomatch i
      | .circle => 3
      | .rectangle => fun | .width => 4 | .height => 2)

end Forms.ExampleForms.Shapes
