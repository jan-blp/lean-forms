module

public import Forms.Model.Component

@[expose] public section

namespace Forms.Runtime

inductive Input where
  | text (value : String)
  | boolean (value : Bool)

inductive ClientBug where
  | unknownControl
  | missingArgument
  | unexpectedArgument
  | wrongArgument (expected : String)
  | unknownOption
  deriving DecidableEq, Repr

instance : ToString ClientBug where
  toString
    | .unknownControl => "Unknown control."
    | .missingArgument => "Missing action argument."
    | .unexpectedArgument => "This action takes no argument."
    | .wrongArgument expected => s!"Expected {expected}."
    | .unknownOption => "Unknown option."

inductive DecodeError where
  | input (message : String)
  | clientBug (error : ClientBug)
  deriving DecidableEq, Repr

instance : ToString DecodeError where
  toString
    | .input message => message
    | .clientBug error => toString error

/-- The whitespace accepted by JavaScript's String.trim. -/
def Input.editorWhitespace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0D) || n == 0x20 || n == 0xA0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
    n == 0x202F || n == 0x205F || n == 0x3000 || n == 0xFEFF

def Input.decode {α : Type} (editor : Model.Editor α) (input : Input) : Except DecodeError α :=
  match editor with
  | .natural => do
    let .text raw := input | throw (.clientBug (.wrongArgument "text"))
    let text := ((raw.dropWhile editorWhitespace).dropEndWhile editorWhitespace).toString
    let some value := if text.all Char.isDigit then text.toNat? else none
      | throw (.input "Enter a non-negative whole number.")
    pure value
  | .text => match input with
    | .text value => .ok value
    | _ => .error (.clientBug (.wrongArgument "text"))
  | .checkbox => match input with
    | .boolean value => .ok value
    | _ => .error (.clientBug (.wrongArgument "a boolean"))

end Forms.Runtime
