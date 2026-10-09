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

abbrev schema : DataType := addressKind

def kind : Path schema addressKind := .self

def initial : DataType.denote schema := .home

open Form Widget in
def form : Form schema schema := field "Kind" select

end Forms.ExampleForms.Person
