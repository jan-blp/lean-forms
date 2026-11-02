import Forms.ExampleForms.Example
import Forms.Runtime.Cli
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

private def runExample
  (selected : Example)
  (theme : NativeTerminal.Theme)
  : IO Unit :=
  let definition := selected.definition
  runComponent theme definition.refined definition.component definition.initial

private def cli : Cli NativeTerminal.Theme where
  examples := (FinEnum.toList Example).map fun selected => (selected.name, runExample selected)
  options := [("--theme", NativeTerminal.Theme.choices)]
  initial := .frappe

def run (args : List String) : IO Unit := cli.run args

end Forms.Application

def main (args : List String) : IO Unit := Forms.Application.run args
