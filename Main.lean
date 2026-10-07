import Forms.ExampleForms.Person
import Forms.Technology.Terminal
import Forms.Technology.NativeTerminal

open Forms.Technology

instance : MonadTerminal IO where
  putStr text := do
    let stdout ← IO.getStdout
    stdout.putStr text
    stdout.flush
  readLine := do
    let stdin ← IO.getStdin
    let line ← stdin.getLine
    if line.isEmpty then
      return none
    return some (line.dropEndWhile (fun char => char == '\n' || char == '\r')).toString

def main (args : List String) : IO Unit := do
  let value ← if List.contains args "--plain" then
      Forms.Technology.Terminal.run Forms.ExampleForms.Person.form Forms.ExampleForms.Person.initial
    else
      NativeTerminal.run Forms.ExampleForms.Person.form Forms.ExampleForms.Person.initial
  MonadTerminal.println "\n  Final values\n  ------------"
  MonadTerminal.println ("  Name        " ++ Forms.Path.get Forms.ExampleForms.Person.name value)
  MonadTerminal.println ("  Subscribed  " ++ toString (Forms.Path.get Forms.ExampleForms.Person.subscribed value))
  MonadTerminal.println ("  Street      " ++ Forms.Path.get Forms.ExampleForms.Person.street value)
  MonadTerminal.println ("  Number      " ++ toString (Forms.Path.get Forms.ExampleForms.Person.number value))
