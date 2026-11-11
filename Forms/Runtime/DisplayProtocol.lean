module

public import Forms.Runtime.Display
public import Forms.Runtime.FeedbackProtocol

@[expose] public section

namespace Forms.Runtime
open Lean

namespace DisplayProtocol
open Display

/-- What a control does to the value at its location. -/
inductive Action where
  | edit
  | select
  | add
  | remove

def Action.name : Action → String
  | .edit => "edit"
  | .select => "select"
  | .add => "add"
  | .remove => "remove"

def stepToJson : Feedback.Step → Json
  | .field name => toJson name
  | .constructor tag => Json.mkObj [("constructor", toJson tag)]
  | .index position => toJson position

/-- Names `action` on the value at `location`, independent of where the control is shown. -/
def controlKey (action : Action) (location : Feedback.Location) : ControlKey :=
  ⟨(Json.arr (#[toJson action.name] ++ (location.map stepToJson).toArray)).compress⟩

def messageFields (messages : Option String) : List (String × Json) :=
  messages.toList.map fun message => ("messages", toJson message)

def widgetName : Editor → String
  | .text _ => "textInput"
  | .natural _ => "naturalInput"
  | .checkbox _ => "checkbox"
  | .choice .. => "choice"
  | .action => "action"

def controlToJson (control : Control) : Json :=
  Json.mkObj ([
    ("key", toJson control.key.value), ("target", toJson control.target.indices),
    ("label", toJson control.label), ("disabled", toJson control.disabled),
    ("kind", toJson "editor"), ("location", FeedbackProtocol.locationToJson control.location),
    ("widget", toJson (widgetName control.input))] ++ messageFields control.messages)

end DisplayProtocol

end Forms.Runtime
