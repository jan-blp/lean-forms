import Forms.Core.Form

namespace Forms.ExampleForms.Person

abbrev person : DataType := .text

def name : Path person .text := .self

def initial : ⟦person⟧ := "Ada"

open Form Widget in
def form : Form person := field "Name" textInput

end Forms.ExampleForms.Person
