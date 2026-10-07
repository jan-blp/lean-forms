import Forms.Technology.Tui

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

instance : MonadTui IO where
  readKey := readKey
  screenSize := screenSize
  draw := draw

def run {root : Ty} (form : Form root root) (value : Ty.denote root)
    : IO (Ty.denote root) := do
  if !(← start) then
    throw (IO.userError "The TUI needs an interactive terminal. Use --plain for line input.")
  try
    Tui.run form value
  finally
    stop

end Forms.Technology.NativeTerminal
