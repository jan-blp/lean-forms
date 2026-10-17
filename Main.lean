import Forms.ExampleForms.Shapes
import Forms.ExampleForms.Location
import Forms.Runtime.Cli
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Person
import Forms.Runtime.NativeTerminal
import Forms.Runtime.Tui

namespace Forms.Application

open ExampleForms Forms.Runtime Composition

private def valueToJson {t : DataType} (value : ⟦t⟧) : Lean.Json :=
  match t with
  | .sum tags constructors => .mkObj [("tag", Lean.toJson (tags.label value.tag)),
      ("value", valueToJson (t := constructors value.tag) value.payload)]
  | .list element => .arr ((value.map (valueToJson (t := element))).toArray)
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson value
  | .date => Lean.toJson (Date.toString value)
  | .enum domain => Lean.toJson (domain.label value)
  | .record fieldNames fieldTypes =>
    .mkObj ((FinEnum.toList fieldNames).map fun i =>
      (fieldNames.label i, valueToJson (t := fieldTypes i) (value i)))

def runForm (theme : NativeTerminal.Theme)
    {context : DataType} (form : Component context) (initial : ⟦context⟧) : IO Unit := do
  let _ : MonadTui IO := NativeTerminal.interpreter theme
  let value ← Tui.run form initial
  IO.println "\n  Final values\n  ------------"
  IO.println (Lean.Json.pretty (valueToJson value))

private def cli : Cli NativeTerminal.Theme where
  examples := [
    ("person", fun theme => runForm theme Person.form Person.initial),
    ("shapes", fun theme => runForm theme Shapes.form Shapes.initial),
    ("location", fun theme => runForm theme Location.form Location.initial),
    ("invoice", fun theme => runForm theme Invoice.form Invoice.initial)]
  options := [("--theme", NativeTerminal.Theme.choices)]
  initial := .frappe

def run (args : List String) : IO Unit := cli.run args

end Forms.Application

def main (args : List String) : IO Unit := Forms.Application.run args
