import Forms.ExampleForms.Counter
import Forms.ExampleForms.Basket
import Forms.ExampleForms.TestReport
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

private def runComponent (theme : NativeTerminal.Theme)
    {state : DataType} (refined : RefinedDataType state)
    (component : Composition.Component state) (draft : ⟦state⟧) : IO Unit := do
  let _ : MonadTui IO := NativeTerminal.interpreter theme
  let result ← Tui.run refined component draft
  match result with
  | none => IO.println "\nCancelled."
  | some value =>
    IO.println "\n  Final values\n  ------------"
    IO.println (Lean.Json.pretty (valueToJson (RefinedDataType.erase refined value)))

private def runCounter (theme : NativeTerminal.Theme) : IO Unit := do
  let _ : MonadTui IO := NativeTerminal.interpreter theme
  let result ← Tui.runWidget (.base .natural) Counter.actionIds "Counter" Counter.actions 0
  match result with
  | none => IO.println "\nCancelled."
  | some result =>
    IO.println "\n  Final values\n  ------------"
    IO.println (ActionHistoryProtocol.encode Counter.actionIds ⟨result.value, result.actions⟩).pretty

private def cli : Cli NativeTerminal.Theme where
  examples := [
    ("person", fun theme => runComponent theme Person.personType Person.form Person.draft),
    ("counter", runCounter),
    ("report", fun theme => runComponent theme (.base TestReport.reportShape) TestReport.report TestReport.initial),
    ("basket", fun theme => runComponent theme (.base Basket.basket) Basket.basketView Basket.initial),
    ("booking", fun theme => runComponent theme Booking.bookingType Booking.form Booking.draft),
    ("location", fun theme => runComponent theme Location.locationType Location.form Location.draft),
    ("shapes", fun theme => runComponent theme Shapes.shapeType Shapes.form Shapes.draft),
    ("invoice", fun theme => runComponent theme Invoice.invoiceType Invoice.form Invoice.draft),
    ("thermostat", fun theme => runComponent theme Thermostat.thermostatType Thermostat.form Thermostat.draft)]
  options := [("--theme", NativeTerminal.Theme.choices)]
  initial := .frappe

def run (args : List String) : IO Unit := cli.run args

end Forms.Application

def main (args : List String) : IO Unit := Forms.Application.run args
