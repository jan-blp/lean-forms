module

public import Forms.Runtime.Display
public import Forms.Runtime.FeedbackProtocol

@[expose] public section

namespace Forms.Runtime.DisplayProtocol
open Lean Display

def targetToJson (target : Target) : Json :=
  toJson (target.map fun step => match step with
    | .name name => toJson name
    | .index index => toJson index)

/-- Preserve the opaque browser key format independently of internal view structure. -/
def controlKey (target : Target) (id : String) (index : Option Nat) : String :=
  (toJson ([targetToJson target, toJson id] ++ index.toList.map toJson)).compress

def messageFields (messages : Option String) : List (String × Json) :=
  messages.toList.map fun message => ("messages", toJson message)

def editorFields : Editor → List (String × Json)
  | .text value => [("widget", toJson "textInput"), ("value", toJson value)]
  | .natural value => [("widget", toJson "naturalInput"), ("value", toJson (toString value))]
  | .date value => [("widget", toJson "dateInput"), ("value", toJson (Date.toString value))]
  | .checkbox value => [("widget", toJson "checkbox"), ("value", toJson value)]
  | .select value options => [("widget", toJson "select"), ("value", toJson value), ("options", toJson options)]

def controlToJson (control : Control) : Json :=
  let fields := match control.body with
    | .button keepDrafts => [("kind", toJson "button"), ("keepDrafts", toJson keepDrafts)]
    | .editor location input => [("kind", toJson "editor"),
        ("location", FeedbackProtocol.locationToJson location)] ++ editorFields input
    | .choice location value options => [("kind", toJson "choice"),
        ("location", FeedbackProtocol.locationToJson location), ("value", toJson value), ("options", toJson options)]
  Json.mkObj ([("key", toJson control.key), ("id", toJson control.id), ("target", targetToJson control.target),
    ("label", toJson control.label), ("disabled", toJson control.disabled)] ++ fields ++ messageFields control.messages)

def viewToJson : View → Json
  | .hidden => .null
  | .control c => controlToJson c
  | .stack label children => Json.mkObj [("kind", toJson "stack"), ("label", toJson label),
      ("children", toJson (children.map viewToJson))]
  | .actionWidget label text location children messages => Json.mkObj
      ([("kind", toJson "actionWidget"), ("label", toJson label), ("text", toJson text),
        ("location", FeedbackProtocol.locationToJson location),
        ("children", toJson (children.map controlToJson))] ++ messageFields messages)
  | .list label location items append messages => Json.mkObj
      ([("kind", toJson "list"), ("label", toJson label), ("location", FeedbackProtocol.locationToJson location),
        ("items", toJson (items.map fun item =>
          Json.mkObj [("body", viewToJson item.1), ("remove", controlToJson item.2)])),
        ("append", controlToJson append)] ++ messageFields messages)
  | .sum selector body => Json.mkObj [("kind", toJson "sum"),
      ("selector", controlToJson selector), ("body", viewToJson body)]
  | .computed label text => Json.mkObj [("kind", toJson "computed"), ("label", toJson label), ("text", toJson text)]
  | .text value => Json.mkObj [("kind", toJson "text"), ("value", toJson value)]
  | .table columns rows => Json.mkObj [("kind", toJson "table"), ("columns", toJson columns), ("rows", toJson rows)]

termination_by view => sizeOf view
decreasing_by
  all_goals first
    | decreasing_trivial
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      have hp : sizeOf item.1 < sizeOf item := by cases item; simp +arith
      simp_wf
      omega

end Forms.Runtime.DisplayProtocol
