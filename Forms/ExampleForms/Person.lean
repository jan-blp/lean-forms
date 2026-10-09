import Forms.Core.Form

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

abbrev address : DataType := .group ![.text, .natural, addressKind]

abbrev schema : DataType := .group ![.text, .boolean, address]

def name : Path schema .text := .child 0 .here

def subscribed : Path schema .boolean := .child 1 .here

def street : Path schema .text := .child 2 (.child 0 .here)

def number : Path schema .natural := .child 2 (.child 1 .here)

def initial : DataType.denote schema
  | 0 => "Ada"
  | 1 => false
  | 2 => fun
    | 0 => "Lambda Lane"
    | 1 => (12 : Nat)
    | 2 => .home

open Form Widget Expr in
def form : Form schema schema :=
  group "Person" fun
    | 0 => field "Name" textInput
    | 1 => field "Subscribed" checkbox
    | 2 => group "Address" fun
      | 0 => visibleWhen (project subscribed) (field "Street" textInput)
      | 1 => visibleWhen (project subscribed) (field "Number" naturalInput)
      | 2 => field "Kind" select

end Forms.ExampleForms.Person
