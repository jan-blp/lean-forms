import Forms.ExampleForms.Person
import Forms.Technology.NativeTerminal
import Forms.Technology.Terminal
import Forms.Technology.Tui

namespace Forms.Application

open ExampleForms Technology

def run
  {m : Type → Type}
  [Monad m]
  [MonadTerminal m]
  [MonadTui m]
  (args : List String)
  : m Unit := do
  let value ←
    if List.contains args "--plain" then
      Terminal.run Person.form Person.initial
    else
      Tui.run Person.form Person.initial

  MonadTerminal.println "\n  Final values\n  ------------"
  let json := Terminal.valueToJson (type := Person.schema) value
  MonadTerminal.println (Lean.Json.pretty json)

end Forms.Application

def main (args : List String) : IO Unit :=
  Forms.Application.run args
