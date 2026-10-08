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

/-- The accepted CLI names, also used by help and shell completion. -/
def Theme.choices : List (String × Theme) :=
  [("frappe", .frappe), ("macchiato", .macchiato), ("mocha", .mocha), ("latte", .latte), ("ayu-light", .ayuLight), ("ayu-dark", .ayuDark), ("nord", .nord)]

def Theme.ofString? (name : String) : Option Theme :=
  (Theme.choices.find? (fun entry => entry.1 == name)).map Prod.snd

private def Theme.toCode (theme : Theme) : UInt8 :=
  match theme with
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
