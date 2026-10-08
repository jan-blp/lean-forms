import Forms.Core.Component.Builder

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

abbrev person : DataType := .record personFields fun
  | .name => .text
  | .subscribed => .boolean
  | .address => address

def name : Path person .text := .field .name .self
def subscribed : Path person .boolean := .field .subscribed .self
def street : Path person .text := .field .address (.field .street .self)
def number : Path person .natural := .field .address (.field .number .self)

def initial : ⟦person⟧
  | .name => "Ada"
  | .subscribed => false
  | .address => fun
    | .street => "Lambda Lane"
    | .number => 12
    | .kind => .home

open Component.Builder Widget Expr in
def form : Component person :=
  (show Component.Builder person person from
    group "Person" fun
      | .name => field "Name" textInput
      | .subscribed => field "Send me postal mail" checkbox
      | .address => group "Address" fun
        | .street => field "Street" textInput
        | .number => field "Number" naturalInput
        | .kind => field "Kind" select) .self

end Forms.ExampleForms.Person
