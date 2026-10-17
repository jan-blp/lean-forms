import Forms.ExampleForms.Booking
import Forms.ExampleForms.Location
import Forms.ExampleForms.Shapes
import Forms.Runtime.Cli
import Forms.ExampleForms.Invoice
import Forms.ExampleForms.Person
import Forms.ExampleForms.Thermostat
import Forms.Runtime.NativeTerminal
import Forms.Runtime.Tui

namespace Forms.Application

open ExampleForms Forms.Runtime

private def valueToJson {t : DataType} (value : DataType.denote t) : Lean.Json :=
  match t with
  | .sum tags constructors => .mkObj [("tag", Lean.toJson (tags.label value.tag)),
      ("value", valueToJson (t := constructors value.tag) value.payload)]
  | .list element => .arr ((value.map (valueToJson (t := element))).toArray)
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson value
  | .date => Lean.toJson (Date.toString value)
  | .enum domain => Lean.toJson (domain.label value)
  | .record fields children =>
    .mkObj ((FinEnum.toList fields).map fun i =>
      (fields.label i, valueToJson (t := children i) (value i)))

def runForm (theme : NativeTerminal.Theme)
  {root : DataType} (refined : RefinedDataType root) (form : Form root root) (initial : RefinedDataType.ValidatedValue refined)
  : IO Unit := do
  let _ : MonadTui IO := NativeTerminal.interpreter theme
  let result ← Tui.run refined form (RefinedDataType.erase refined initial)
  match result with
  | none => IO.println "\nCancelled."
  | some value =>
    IO.println "\n  Final values\n  ------------"
    IO.println (Lean.Json.pretty (valueToJson (RefinedDataType.erase refined value)))

private def cli : Cli NativeTerminal.Theme where
  examples := [
    ("person", fun theme => runForm theme Person.personType Person.form Person.initial),
    ("booking", fun theme => runForm theme Booking.bookingType Booking.form Booking.initial),
    ("location", fun theme => runForm theme Location.locationType Location.form Location.initial),
    ("shapes", fun theme => runForm theme Shapes.shapeType Shapes.form Shapes.initial),
    ("invoice", fun theme => runForm theme Invoice.invoiceType Invoice.form Invoice.initial),
    ("thermostat", fun theme => runForm theme Thermostat.thermostatType Thermostat.form Thermostat.initial)]
  options := [("--theme", NativeTerminal.Theme.choices)]
  initial := .frappe

def run (args : List String) : IO Unit := cli.run args

end Forms.Application

def main (args : List String) : IO Unit := Forms.Application.run args
