import Forms.ExampleForms.Person
import Forms.Runtime.NativeTerminal
import Forms.Runtime.Tui

private structure ThemeOptions where
  theme : Forms.Runtime.NativeTerminal.Theme := .frappe

private def parseThemeArgs : List String → ThemeOptions → Except String ThemeOptions
  | [], options => .ok options
  | "--theme" :: name :: rest, options => do
    let some theme := Forms.Runtime.NativeTerminal.Theme.ofString? name
      | throw s!"Unknown theme: {name}. Choose frappe, macchiato, mocha, latte, ayu-light, ayu-dark, or nord"
    parseThemeArgs rest { options with theme := theme }
  | ["--theme"], _ => .error "Expected a theme name after --theme"
  | arg :: _, _ => .error s!"Unknown option: {arg}"

namespace Forms.Application

open ExampleForms Forms.Runtime

private def valueToJson {type : DataType} (value : DataType.denote type) : Lean.Json :=
  match type with
  | .text => Lean.toJson value
  | .boolean => Lean.toJson value
  | .natural => Lean.toJson value
  | .choice domain => Lean.toJson (domain.label value)
  | .group children =>
    .arr (Array.ofFn fun i => valueToJson (type := children i) (value i))

def run (theme : NativeTerminal.Theme) : IO Unit := do
  let _ : MonadTui IO := NativeTerminal.interpreter theme
  let value ← Tui.run Person.form Person.initial
  IO.println "\n  Final values\n  ------------"
  IO.println (Lean.Json.pretty (valueToJson (type := Person.schema) value))

end Forms.Application

def main (args : List String) : IO Unit := do
  let options ← IO.ofExcept (parseThemeArgs args {})
  Forms.Application.run options.theme
