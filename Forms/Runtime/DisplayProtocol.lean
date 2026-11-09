module

public import Forms.Runtime.Display
public import Forms.Runtime.FeedbackProtocol

@[expose] public section

namespace Forms.Runtime
open Lean

namespace DisplayProtocol
open Display

def controlKey (target : Target) : ControlKey :=
  ⟨(toJson target.indices).compress⟩

def messageFields (messages : Option String) : List (String × Json) :=
  messages.toList.map fun message => ("messages", toJson message)

def widgetName : Editor → String
  | .text _ => "textInput"
  | .natural _ => "naturalInput"
  | .checkbox _ => "checkbox"
  | .choice .. => "choice"

def controlToJson (control : Control) : Json :=
  Json.mkObj ([
    ("key", toJson control.key.value), ("target", toJson control.target.indices),
    ("label", toJson control.label), ("disabled", toJson control.disabled),
    ("kind", toJson "editor"), ("location", FeedbackProtocol.locationToJson control.location),
    ("widget", toJson (widgetName control.input))] ++ messageFields control.messages)

end DisplayProtocol

end Forms.Runtime
