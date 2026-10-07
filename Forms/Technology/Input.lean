import Forms.Domain.Model

namespace Forms.Technology

inductive InputError where
  | expectedBoolean
  | expectedNatural
  deriving Repr, BEq

def parse {type : Ty} (control : Control type) (input : String) : Except InputError (Ty.denote type) :=
  match control with
  | .text => .ok input
  | .checkbox =>
    match input.trimAscii.toString with
    | "true" => .ok true
    | "false" => .ok false
    | _ => .error .expectedBoolean
  | .natural =>
    match input.trimAscii.toString.toNat? with
    | some number => .ok number
    | none => .error .expectedNatural

def edit {root : Ty} (field : FieldRef root) (input : String)
    (value : Ty.denote root) : Except InputError (Ty.denote root) :=
  Except.map (fun replacement => Path.set field.path replacement value)
    (parse field.control input)

def display {type : Ty} (control : Control type) (value : Ty.denote type) : String :=
  match control with
  | .text => value
  | .checkbox => if value then "true" else "false"
  | .natural => toString value

def InputError.message (error : InputError) : String :=
  match error with
  | .expectedBoolean => "Enter true or false."
  | .expectedNatural => "Enter a non-negative whole number."

end Forms.Technology
