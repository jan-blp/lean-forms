import Forms.Core.Form

namespace Forms.ExampleForms.Person

abbrev schema : DataType := .text

def name : Path schema .text := .self

def initial : DataType.denote schema := "Ada"

open Form Widget in
def form : Form schema schema := field "Name" textInput

end Forms.ExampleForms.Person
