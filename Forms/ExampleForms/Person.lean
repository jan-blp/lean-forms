import Forms.Core.Form

namespace Forms.ExampleForms.Person

inductive AddressField where
  | street | number
  deriving DecidableEq, Repr

instance : FinEnum AddressField :=
  FinEnum.ofList [.street, .number] (by grind [AddressField])

def addressFields : Enum where
  type := AddressField
  label
    | .street => "street"
    | .number => "number"

inductive PersonField where
  | name | subscribed | address
  deriving DecidableEq, Repr

instance : FinEnum PersonField :=
  FinEnum.ofList [.name, .subscribed, .address] (by grind [PersonField])

def personFields : Enum where
  type := PersonField
  label
    | .name => "name"
    | .subscribed => "subscribed"
    | .address => "address"

abbrev address : DataType := .record addressFields fun
  | .street => .text
  | .number => .natural

abbrev schema : DataType := .record personFields fun
  | .name => .text
  | .subscribed => .boolean
  | .address => address

def name : Path schema .text := .child .name .self
def subscribed : Path schema .boolean := .child .subscribed .self
def street : Path schema .text := .child .address (.child .street .self)
def number : Path schema .natural := .child .address (.child .number .self)

def initial : DataType.denote schema
  | .name => "Ada"
  | .subscribed => false
  | .address => fun
    | .street => "Lambda Lane"
    | .number => 12

open Form Widget Expr in
def form : Form schema schema :=
  group "Person" fun
    | .name => field "Name" textInput
    | .subscribed => field "Subscribed" checkbox
    | .address => visibleWhen (project subscribed) (group "Address" fun
      | .street => field "Street" textInput
      | .number => field "Number" naturalInput)

end Forms.ExampleForms.Person
