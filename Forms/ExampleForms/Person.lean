import Forms.Core.Form
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Person

inductive AddressKind where
  | home
  | work
  | other
  deriving DecidableEq, BEq, Repr

instance : FinEnum AddressKind :=
  FinEnum.ofList [.home, .work, .other] (by grind [AddressKind])

def addressChoices : Choice where
  type := AddressKind
  label
    | .home => "Home"
    | .work => "Work"
    | .other => "Other"
  label_injective := by
    grind [Function.Injective, AddressKind]

abbrev addressKind : DataType := .choice addressChoices

abbrev address : DataType := .group ![.text, addressKind]

abbrev shape : DataType := .group ![.text, .natural, .boolean, address]

def name : Path shape .text := .child 0 .here

def age : Path shape .natural := .child 1 .here

def subscribed : Path shape .boolean := .child 2 .here

def street : Path shape .text := .child 3 (.child 0 .here)

def ageType : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .and (.natLe (.value 18) (.project .here))
        (.natLe (.project .here) (.value 120))
      errorMessage := "Attendees must be between 18 and 120 years old."
      errorLocation := some ⟨.here⟩ }

def personType : RefinedDataType shape :=
  .group fun
    | 0 => .base .text
    | 1 => ageType
    | 2 => .base .boolean
    | 3 => .base address

def initial : personType.denote
  | 0 => "Ada"
  | 1 => ⟨(28 : Nat), by decide⟩
  | 2 => false
  | 3 => fun
    | 0 => "Lambda Lane"
    | 1 => .home

def draft : DataType.denote shape := personType.erase initial

open Form Widget Expr in
def form : Form shape shape :=
  group "Registration" fun
    | 0 => field "Name" textInput
    | 1 => field "Age (18-120)" naturalInput
    | 2 => field "Subscribed" checkbox
    | 3 => group "Address" fun
      | 0 => visibleWhen (project subscribed) (field "Street" textInput)
      | 1 => field "Kind" select

end Forms.ExampleForms.Person
