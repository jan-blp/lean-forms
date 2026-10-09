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

abbrev person : DataType := addressKind

def kind : Path person addressKind := .self

def initial : DataType.denote person := .home

open Form Widget in
def form : Form person person := field "Kind" select

end Forms.ExampleForms.Person
