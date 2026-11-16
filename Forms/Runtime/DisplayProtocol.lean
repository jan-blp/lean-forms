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
  | .text .plain _ => "textInput"
  | .text .natural _ => "naturalInput"
  | .text .integer _ => "integerInput"
  | .text .decimal _ => "decimalInput"
  | .text .date _ => "dateInput"
  | .text .uuid _ => "uuidInput"
  | .checkbox _ => "checkbox"
  | .choice .. => "choice"
  | .choices .. => "choices"
  | .action => "action"
  | .tabs .. => "tabs"

def controlToJson (control : Control) : Json :=
  Json.mkObj ([
    ("key", toJson (ControlKeyProtocol.toString control.key)), ("target", toJson control.target.indices),
    ("label", toJson control.label), ("disabled", toJson control.disabled),
    ("kind", toJson "editor"), ("location", FeedbackProtocol.locationToJson control.location),
    ("widget", toJson (widgetName control.input)), ("messages", toJson control.messages)])

end DisplayProtocol

end Forms.Runtime
