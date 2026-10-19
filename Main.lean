import Forms.Runtime.Cli
import Forms.ExampleForms.Person
import Forms.Runtime.NativeTerminal
import Forms.Runtime.Tui

namespace Forms.Application

open ExampleForms Forms.Runtime

private def valueToJson {type : DataType} (value : DataType.denote type) : Lean.Json :=
  match type with
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson value
  | .date => Lean.toJson (Date.toString value)
  | .enum domain => Lean.toJson (domain.label value)

private def runForm {root : DataType} (form : Form root root)
    (initial : DataType.denote root) (theme : NativeTerminal.Theme) : IO Unit := do
  let _ : MonadTui IO := NativeTerminal.interpreter theme
  let value ← Tui.run form initial
  IO.println "\n  Final values\n  ------------"
  IO.println (Lean.Json.pretty (valueToJson value))

private def runPerson (theme : NativeTerminal.Theme) : IO Unit :=
  runForm Person.form Person.initial theme

private def runEnum (theme : NativeTerminal.Theme) : IO Unit :=
  runForm (root := Person.addressKind) (.field "Kind" .select) .home theme

private def cli : Cli NativeTerminal.Theme where
  examples := [("person", runPerson), ("enum", runEnum)]
  options := [("--theme", NativeTerminal.Theme.choices)]
  initial := .frappe

def run (args : List String) : IO Unit := cli.run args

end Forms.Application

def main (args : List String) : IO Unit := Forms.Application.run args
