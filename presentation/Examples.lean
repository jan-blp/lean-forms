-- Check against the "add tuples and groups" revision (41f41f5).
-- From that checkout: lake env lean -DwarningAsError=true /path/to/Examples.lean
import Forms.ExampleForms.Person
import Forms.Runtime.Tui

namespace Forms.Presentation
open scoped Forms.DependentVec

def nameForm : Form .text .text := .field "Name" .textInput
def nameValue : DataType.denote .text := "Ada"
def subscribed : Form .boolean .boolean := .field "Subscribed" .checkbox

abbrev address : DataType := .tuple ![.text, .natural]
abbrev schema : DataType := .tuple ![.text, .boolean, address]

def initial : DataType.denote schema :=
  !["Ada", false, !["Lambda Lane", (12 : Nat)]]

def form : Form schema schema :=
  .group "Person" ![
    .field "Name" .textInput,
    .field "Subscribed" .checkbox,
    .group "Address" ![
      .field "Street" .textInput,
      .field "Number" .naturalInput]]

def number : Path schema .natural := .field 2 (.field 1 .here)
def updated : DataType.denote schema := Path.set number 42 initial

def atLeastTen : Expr schema .boolean :=
  .natLe (.value 10) (.project number)

example : initial 0 = ("Ada" : String) := rfl
example : initial 1 = false := rfl
example : (initial 2) 1 = (12 : Nat) := rfl
#guard Path.get number initial == 12
#guard Path.get number updated == 42
example : updated 0 = initial 0 := rfl
#guard Expr.eval atLeastTen initial

example : Form .text .text := .field "Name" .textInput
abbrev schemaChildren : Fin 3 → DataType := ![.text, .boolean, address]
example : DataType.denote schema = ((i : Fin 3) → DataType.denote (schemaChildren i)) := rfl

-- These failures are part of the presentation's static-safety examples.
example : True := by
  fail_if_success have : Form .text .text := .field "Name" .checkbox
  fail_if_success have := Path.set number "forty-two" initial
  fail_if_success have : DataType.denote schema :=
    ![false, "Ada", !["Lambda Lane", (12 : Nat)]]
  trivial

def run {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m]
    [Runtime.MonadTui m] : m (DataType.denote schema) :=
  Runtime.Tui.run form initial

#guard (Runtime.JsonProtocol.valueFromJson schema
  (Lean.Json.arr #[Lean.toJson "Ada", Lean.toJson true,
    Lean.Json.arr #[Lean.toJson "Lambda Lane", Lean.toJson "42"]])).isOk

end Forms.Presentation
