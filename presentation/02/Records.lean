import Forms.ExampleForms.Person
import Forms.Core.Component.Builder
import Forms.Runtime.FormSnapshot

namespace Forms.Presentation.Records

open Composition
open Forms.ExampleForms.Person (addressKind)

inductive AddressField where
  | street
  | number
  | kind
  deriving DecidableEq

instance : FinEnum AddressField :=
  FinEnum.ofList [.street, .number, .kind] (by grind [AddressField])

def addressFields : Enum where
  type := AddressField
  label
    | .street => "street"
    | .number => "number"
    | .kind => "kind"

abbrev address : DataType := .record addressFields fun
  | .street => .text
  | .number => .natural
  | .kind => addressKind

def addressForm : Component address :=
  .stack (some "Address") (items := addressFields) (fun
    | .street => .field (.field .street .self) "Street" .textInput
    | .number => .field (.field .number .self) "Number" .naturalInput
    | .kind => .field (.field .kind .self) "Kind" .select)

open Component in
def addressFormWithGroup : Component address :=
  Builder.group (fields := addressFields) "Address" (children := fun
    | .street => Builder.field "Street" .textInput
    | .number => Builder.field "Number" .naturalInput
    | .kind => Builder.field "Kind" .select)
  |>.build

def initialAddress : ⟦address⟧
  | .street => "Lambda Lane"
  | .number => 12
  | .kind => .home

#guard (Runtime.FormSnapshot.render addressForm initialAddress).fieldRefs.length == 3
#guard (Runtime.FormSnapshot.render addressForm initialAddress).fieldRefs.map (·.labels) ==
  [["Address", "Street"], ["Address", "Number"], ["Address", "Kind"]]

example : True := by
  fail_if_success have : Component address := .field (.field .street .self) "Street" .checkbox
  trivial

end Forms.Presentation.Records
