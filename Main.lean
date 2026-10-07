import Forms.ExampleForms.Person
import Forms.Runtime.Terminal

open Forms.Runtime

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

def main : IO Unit := do
  MonadTerminal.println "\n  LEAN FORMS\n  ----------"
  let value ← Forms.Runtime.Terminal.run Forms.ExampleForms.Person.form Forms.ExampleForms.Person.initial
  MonadTerminal.println "\n  Final values\n  ------------"
  MonadTerminal.println ("  Name        " ++ Forms.Path.get Forms.ExampleForms.Person.name value)
