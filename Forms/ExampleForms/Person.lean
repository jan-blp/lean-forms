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

def addressEnum : Enum where
  type := AddressKind
  label kind :=
    match kind with
    | .home => "Home"
    | .work => "Work"
    | .other => "Other"

abbrev addressKind : DataType := .enum addressEnum

inductive AddressField where
  | street | kind
  deriving DecidableEq, Repr

instance : FinEnum AddressField :=
  FinEnum.ofList [.street, .kind] (by grind [AddressField])

def addressFields : Enum where
  type := AddressField
  label
    | .street => "street"
    | .kind => "kind"

inductive PersonField where
  | name | age | subscribed | address
  deriving DecidableEq, Repr

instance : FinEnum PersonField :=
  FinEnum.ofList [.name, .age, .subscribed, .address] (by grind [PersonField])

def personFields : Enum where
  type := PersonField
  label
    | .name => "name"
    | .age => "age"
    | .subscribed => "subscribed"
    | .address => "address"

abbrev address : DataType := .record addressFields fun
  | .street => .text
  | .kind => addressKind

abbrev shape : DataType := .record personFields fun
  | .name => .text
  | .age => .natural
  | .subscribed => .boolean
  | .address => address

def name : Path shape .text := .child .name .self
def age : Path shape .natural := .child .age .self
def subscribed : Path shape .boolean := .child .subscribed .self
def street : Path shape .text := .child .address (.child .street .self)

def ageType : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .and (.natLe (.value 18) (.project .self))
        (.natLe (.project .self) (.value 120))
      errorMessage := "Attendees must be between 18 and 120 years old."
      errorLocation := some ⟨.self⟩ }

def personType : RefinedDataType shape :=
  .record fun
    | .name => .base .text
    | .age => ageType
    | .subscribed => .base .boolean
    | .address => .base address

def initial : RefinedDataType.ValidatedValue personType
  | .name => "Ada"
  | .age => ⟨(28 : Nat), by decide⟩
  | .subscribed => false
  | .address => fun
    | .street => "Lambda Lane"
    | .kind => .home

def draft : DataType.denote shape := RefinedDataType.erase personType initial

open Form Widget Expr in
def form : Form shape shape :=
  group "Registration" fun
    | .name => field "Name" textInput
    | .age => field "Age (18-120)" naturalInput
    | .subscribed => field "Subscribed" checkbox
    | .address => group "Address" fun
      | .street => visibleWhen (project subscribed) (field "Street" textInput)
      | .kind => field "Kind" select

end Forms.ExampleForms.Person
