-- Check at presentation-1 ("add enum"):
-- lake env lean -DwarningAsError=true /path/to/presentation/01/Examples.lean
import Forms.ExampleForms.Person
import Forms.Runtime.Tui

namespace Forms.Presentation

def nameForm : Form .text := .field "Name" .textInput
def nameValue : DataType.denote .text := "Ada"
def subscribed : Form .boolean := .field "Send me postal mail" .checkbox
def dateForm : Form .date := .field "Date" .dateInput

def kindForm : Form Forms.ExampleForms.Person.addressKind := .field "Kind" .select

#guard (Form.fieldRefs nameForm).length == 1
#guard (Form.fieldRefs kindForm).length == 1
#guard (Runtime.JsonProtocol.valueFromJson .text (Lean.toJson nameValue)).isOk

example : True := by
  fail_if_success have : Form .text := .field "Name" .checkbox
  fail_if_success have : DataType.denote .natural := "forty-two"
  trivial

def run {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m]
    [Runtime.MonadTui m] : m String :=
  Runtime.Tui.run nameForm nameValue

end Forms.Presentation
