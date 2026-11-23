module

public import Forms.Runtime.Display
public import Forms.Runtime.ControlKeyProtocol
public import Forms.Runtime.FeedbackProtocol

@[expose] public section

namespace Forms.Runtime
open Lean

namespace DisplayProtocol
open Display

def widgetName : Editor → String
  | .field (.text .plain _) _ => "textInput"
  | .field (.text .natural _) _ => "naturalInput"
  | .field (.text .integer _) _ => "integerInput"
  | .field (.text .decimal _) _ => "decimalInput"
  | .field (.text .date _) _ => "dateInput"
  | .field (.text .uuid _) _ => "uuidInput"
  | .field (.checkbox _) _ => "checkbox"
  | .field (.choices ..) _ => "choices"
  | .choice .. => "choice"
  | .action => "action"
  | .tabs .. => "tabs"

def controlToJson (control : Control) : Json :=
  Json.mkObj ([
    ("key", toJson (ControlKeyProtocol.toString control.key)), ("target", toJson control.target.indices),
    ("label", toJson control.label), ("disabled", toJson control.disabled),
    ("kind", toJson "editor"), ("location", FeedbackProtocol.locationToJson control.location),
    ("widget", toJson (widgetName control.input)),
    ("messages", toJson (Model.Message.errors control.messages)),
    ("reports", toJson (control.messages.filterMap fun message => match message.kind with
      | .error => none
      | .report kind =>
        some (Json.mkObj [("message", toJson message.text), ("kind", toJson kind)])))])

end DisplayProtocol

end Forms.Runtime
