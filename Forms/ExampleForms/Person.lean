import Forms.Core.Form

namespace Forms.ExampleForms.Person

abbrev address : DataType := .group ![.text, .natural]

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

open Form Widget Expr in
def form : Form schema schema :=
  group "Person" fun
    | 0 => field "Name" textInput
    | 1 => field "Subscribed" checkbox
    | 2 => visibleWhen (project subscribed) (group "Address" fun
      | 0 => field "Street" textInput
      | 1 => field "Number" naturalInput)

end Forms.ExampleForms.Person
