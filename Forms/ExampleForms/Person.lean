import Forms.Core.Form

namespace Forms.ExampleForms.Person

inductive AddressKind where
  | home
  | work
  | other
  deriving DecidableEq, BEq, Repr

instance : FinEnum AddressKind :=
  FinEnum.ofList [.home, .work, .other] (by grind [AddressKind])

def addressEnum : Enum where
  type := AddressKind
  label kind :=
    match kind with
    | .home => "Home"
    | .work => "Work"
    | .other => "Other"
  label_injective := by
    grind [Function.Injective, AddressKind]

abbrev addressKind : DataType := .enum addressEnum

inductive AddressField where
  | street | number | kind
  deriving DecidableEq, Repr

instance : FinEnum AddressField :=
  FinEnum.ofList [.street, .number, .kind] (by grind [AddressField])

def addressFields : Enum where
  type := AddressField
  label
    | .street => "street"
    | .number => "number"
    | .kind => "kind"

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
  | .kind => addressKind

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
    | .kind => .home

open Form Widget Expr in
def form : Form schema schema :=
  group "Person" fun
    | .name => field "Name" textInput
    | .subscribed => field "Subscribed" checkbox
    | .address => group "Address" fun
      | .street => visibleWhen (project subscribed) (field "Street" textInput)
      | .number => visibleWhen (project subscribed) (field "Number" naturalInput)
      | .kind => field "Kind" select

end Forms.ExampleForms.Person
