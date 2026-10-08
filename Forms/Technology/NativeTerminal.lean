import Forms.Technology.Tui
import Forms.Technology.Terminal

namespace Forms.Technology.NativeTerminal

@[extern "forms_terminal_run"]
private opaque runSpecification (specification : @& String) : IO String

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

instance : MonadTui IO where
  runSpecification := runSpecification

end Forms.Technology.NativeTerminal
