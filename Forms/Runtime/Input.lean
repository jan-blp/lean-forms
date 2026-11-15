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

def Input.decode {α : Type} (editor : Model.Editor α) (input : Input) : Except DecodeError α :=
  match editor with
  | .formatted format => match input with
    | .text raw => (format.parse raw).mapError .input
    | _ => .error (.clientBug (.wrongArgument "text"))
  | .checkbox => match input with
    | .boolean value => .ok value
    | _ => .error (.clientBug (.wrongArgument "a boolean"))

end Forms.Runtime
