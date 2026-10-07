import Forms.Runtime.Input

namespace Forms.Runtime

class MonadTerminal (m : Type → Type) where
  putStr : String → m Unit
  /-- Reads a line without its line ending; `none` means end of input. -/
  readLine : m (Option String)

def MonadTerminal.println {m : Type → Type} [MonadTerminal m] (text : String) : m Unit :=
  MonadTerminal.putStr (text ++ "\n")

namespace Terminal

variable {m : Type → Type} [Monad m] [MonadTerminal m]

private def readLine (prompt : String) : m (Option String) := do
  MonadTerminal.putStr prompt
  MonadTerminal.readLine

private def fieldLabel {root : DataType} (field : FieldRef root) : String :=
  String.intercalate "." (Path.Labels.toList field.labels)

private def padRight (width : Nat) (text : String) : String :=
  text ++ String.ofList (List.replicate (width - String.length text) ' ')

private def fieldValue {root : DataType} (field : FieldRef root) (value : DataType.denote root) : String :=
  let text := display field.control (Path.get field.path value)
  if String.isEmpty text then "(empty)" else text

private def inputHint {type : DataType} (control : Control type) : String :=
  match control with
  | .text => "text; an empty line clears the field"
  | .checkbox => "true or false"
  | .natural => "whole number, 0 or greater"

private def showFields {root : DataType} (fields : List (FieldRef root))
    (value : DataType.denote root) : m Unit := do
  let labelWidth := List.foldl (fun width field =>
    max width (String.length (fieldLabel field))) 0 fields
  let numberWidth := String.length (toString (List.length fields))
  MonadTerminal.println ""
  for (field, index) in List.zipIdx fields do
    let number := padRight numberWidth (toString (index + 1))
    let label := padRight labelWidth (fieldLabel field)
    MonadTerminal.println ("  " ++ number ++ "  " ++ label ++ "  " ++ fieldValue field value)
  if List.isEmpty fields then
    MonadTerminal.println "  No fields are currently visible."
  MonadTerminal.println ""

partial def run {root : DataType} (form : Form root root) (value : DataType.denote root) : m (DataType.denote root) := do
  let fields := Form.fieldRefs form value
  showFields fields value
  match ← readLine "  Edit field number, or q to finish > " with
  | none => return value
  | some "q" => return value
  | some command =>
    let selected := do
      let number ← command.toNat?
      if number == 0 then none else fields[number - 1]?
    match selected with
    | none =>
      MonadTerminal.println "Choose one of the displayed field numbers."
      run form value
    | some field =>
      MonadTerminal.println ""
      MonadTerminal.println ("  " ++ fieldLabel field)
      MonadTerminal.println ("  Current: " ++ fieldValue field value)
      MonadTerminal.println ("  Enter " ++ inputHint field.control ++ ".")
      match ← readLine "  New value > " with
      | none => return value
      | some input =>
        match edit field input value with
        | .error error =>
          MonadTerminal.println (InputError.message error)
          run form value
        | .ok edited => run form edited

end Terminal

end Forms.Runtime
