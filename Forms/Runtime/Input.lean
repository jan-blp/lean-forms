module

public import Forms.Model.Component

@[expose] public section

namespace Forms.Runtime

inductive LookupInput where
  | search (text : String)
  | close
  | choose (key : Model.LookupKey)
  | clear
  deriving DecidableEq, Repr, Lean.ToJson, Lean.FromJson

inductive Input where
  | text (value : String)
  | boolean (value : Bool)
  | texts (values : List String)
  | pick (evidence : Model.Evidence)
  | lookup (input : LookupInput)

/-- Whether the input is text the user typed, which stays in the field as a draft when rejected. -/
def Input.typed : Input → Bool
  | .text _ => true
  | .boolean _ => false
  | .texts _ => false
  | .pick _ => false
  | .lookup _ => false

inductive ClientBug where
  | missingArgument
  | unexpectedArgument
  | wrongArgument (expected : String)
  | unknownOption
  | noEvidence
  deriving DecidableEq, Repr

instance : ToString ClientBug where
  toString
    | .missingArgument => "Missing action argument."
    | .unexpectedArgument => "This action takes no argument."
    | .wrongArgument expected => s!"Expected {expected}."
    | .unknownOption => "Unknown option."
    | .noEvidence => "This field takes no evidence."

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
  | .choices (key := _) { options, .. } _ => match input with
    | .texts keys =>
      if keys.all fun key => options.any (Model.Key.encode ·.key == key) then
        .ok (options.filter (keys.contains <| Model.Key.encode ·.key) |>.map (·.start))
      else .error (.clientBug .unknownOption)
    | _ => .error (.clientBug (.wrongArgument "a list of options"))
  | .refine editor _ parse _ => do
    (parse (← Input.decode editor input)).mapError .input
  | .whileTyping editor => Input.decode editor input

end Forms.Runtime
