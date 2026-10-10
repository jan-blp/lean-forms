import Forms.ExampleForms.Person
import Forms.ExampleForms.Thermostat
import Forms.Runtime.NativeTerminal
import Forms.Runtime.Tui

namespace Forms.Application

open ExampleForms Forms.Runtime

private def valueToJson {t : DataType} (value : DataType.denote t) : Lean.Json :=
  match t with
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson value
  | .choice domain => Lean.toJson (domain.label value)
  | .group children =>
    .arr (Array.ofFn fun i => valueToJson (t := children i) (value i))

def runForm (theme : NativeTerminal.Theme)
  {root : DataType} (refined : RefinedDataType root) (form : Form root root) (initial : refined.denote)
  : IO Unit := do
  let _ : MonadTui IO := NativeTerminal.interpreter theme
  let result ← Tui.run refined form (refined.erase initial)
  match result with
  | none => IO.println "\nCancelled."
  | some value =>
    IO.println "\n  Final values\n  ------------"
    IO.println (Lean.Json.pretty (valueToJson (refined.erase value)))

private structure Options where
  theme : NativeTerminal.Theme := .frappe
  thermostat : Bool := false

private def parseArgs : List String → Options → Except String Options
  | [], options => .ok options
  | "--thermostat" :: rest, options => parseArgs rest { options with thermostat := true }
  | "--theme" :: name :: rest, options => do
    let some theme := NativeTerminal.Theme.ofString? name
      | throw s!"Unknown theme: {name}. Choose frappe, macchiato, mocha, latte, ayu-light, ayu-dark, or nord"
    parseArgs rest { options with theme := theme }
  | ["--theme"], _ => .error "Expected a theme name after --theme"
  | arg :: _, _ => .error s!"Unknown option: {arg}"

def run (args : List String) : IO Unit := do
  let options ← IO.ofExcept (parseArgs args {})
  if options.thermostat then
    runForm options.theme Thermostat.thermostatType Thermostat.form Thermostat.initial
  else runForm options.theme Person.personType Person.form Person.initial

end Forms.Application

def main (args : List String) : IO Unit :=
  Forms.Application.run args
