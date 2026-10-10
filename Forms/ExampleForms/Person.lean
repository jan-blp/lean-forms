import Forms.Core.Component.Builder
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Person
open Composition

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

abbrev person : DataType := .record personFields fun
  | .name => .text
  | .age => .natural
  | .subscribed => .boolean
  | .address => address

def name : Path person .text := .field .name .self
def age : Path person .natural := .field .age .self
def subscribed : Path person .boolean := .field .subscribed .self
def street : Path person .text := .field .address (.field .street .self)

def ageType : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .and (.natLe (.value 18) (.project .self))
        (.natLe (.project .self) (.value 120))
      errorMessage := "Attendees must be between 18 and 120 years old."
      errorLocation := some ⟨.self⟩ }

def personType : RefinedDataType person :=
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

def draft : ⟦person⟧ := RefinedDataType.erase personType initial

open Component.Builder Widget Expr in
def form : Component person :=
  (show Component.Builder person person from
    group "Registration" fun
      | .name => field "Name" textInput
      | .age => field "Age (18-120)" naturalInput
      | .subscribed => field "Send me postal mail" checkbox
      | .address => visibleWhen (project subscribed) (group "Address" fun
        | .street => field "Street" textInput
        | .kind => field "Kind" select)) .self

end Forms.ExampleForms.Person
