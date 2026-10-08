import Forms.Runtime.Tui

namespace Forms.Runtime.NativeTerminal

inductive Theme where
  | frappe
  | macchiato
  | mocha
  | latte
  | ayuLight
  | ayuDark
  | nord

def Theme.ofString? : String → Option Theme
  | "frappe" => some .frappe
  | "macchiato" => some .macchiato
  | "mocha" => some .mocha
  | "latte" => some .latte
  | "ayu-light" => some .ayuLight
  | "ayu-dark" => some .ayuDark
  | "nord" => some .nord
  | _ => none

private def Theme.toCode : Theme → UInt8
  | .frappe => 0
  | .macchiato => 1
  | .mocha => 2
  | .latte => 3
  | .ayuLight => 4
  | .ayuDark => 5
  | .nord => 6

@[extern "forms_terminal_run"]
private opaque runSpecification (specification : @& String) (theme : UInt8) : IO String

@[instance_reducible] def interpreter (theme : Theme) : MonadTui IO where
  runSpecification specification := runSpecification specification theme.toCode

instance : MonadTui IO := interpreter .frappe

end Forms.Runtime.NativeTerminal
