import Forms.Core.Form

namespace Forms.ExampleForms.Person

abbrev person : DataType := .text

def name : Path person .text := .self

def initial : DataType.denote person := "Ada"

open Form Widget in
def form : Form person person := field "Name" textInput

end Forms.ExampleForms.Person
