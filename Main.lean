import Forms.ExampleForms.Counter
import Forms.ExampleForms.Counters
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

private def runComponent
  (theme : NativeTerminal.Theme)
  {state : DataType}
  (refined : RefinedDataType state)
  (component : Composition.Component state)
  (draft : ⟦state⟧)
  : IO Unit := do
  let _ : MonadTui IO := NativeTerminal.interpreter theme
  let result ← Tui.run refined component draft
  match result with
  | none => IO.println "\nCancelled."
  | some result =>
    IO.println "\n  Final values\n  ------------"
    let value := RefinedDataType.erase refined result.value
    IO.println (ComponentHistoryProtocol.encode (component := component) ⟨value, result.actions⟩).pretty

private def cli : Cli NativeTerminal.Theme where
  examples := [
    ("person", fun theme => runComponent theme Person.personType Person.form Person.draft),
    ("counter", fun theme => runComponent theme (.base .natural) Counter.form 0),
    ("counters", fun theme => runComponent theme (.base Counters.state) Counters.form Counters.initial),
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
