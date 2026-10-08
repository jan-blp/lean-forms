import Forms.Technology.Tui
import Forms.Technology.Terminal

namespace Forms.Technology.NativeTerminal

@[extern "forms_terminal_start"]
private opaque start : IO Bool

@[extern "forms_terminal_stop"]
private opaque stop : IO Unit

@[extern "forms_terminal_key"]
private opaque nextKey : IO UInt32

@[extern "forms_terminal_size"]
private opaque dimensions : IO UInt32

@[extern "forms_terminal_draw"]
private opaque drawScreen (fields : @& Array ScreenField) (selected : USize)
    (editor : @& Option ScreenEditor) : IO Unit

private def screenSize : IO ScreenSize := do
  let packed ← dimensions
  return {
    columns := UInt32.toNat (packed % 65536)
    rows := UInt32.toNat (packed / 65536)
  }

private def readKey : IO Key := do
  let key ← nextKey
  return match key with
    | 1 => .up
    | 2 => .down
    | 3 => .enter
    | 4 => .escape
    | 5 => .backspace
    | 6 => .clear
    | 7 => .quit
    | _ => if key >= 256 then .character (Char.ofNat (UInt32.toNat key - 256)) else .refresh

private def draw (screen : Screen) : IO Unit :=
  drawScreen (List.toArray screen.fields) (USize.ofNat screen.selected) screen.editor

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

private def withSession {α : Type} (action : IO α) : IO α := do
  if !(← start) then
    throw (IO.userError "The TUI needs an interactive terminal. Use --plain for line input.")
  try
    action
  finally
    stop

instance : MonadTui IO where
  readKey := readKey
  screenSize := screenSize
  draw := draw
  withSession := withSession

end Forms.Technology.NativeTerminal
