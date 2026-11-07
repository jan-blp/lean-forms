module

public import Forms.Runtime.DisplayLayout
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

def tagName : DisplayLayout.Tag → String
  | .div => "div" | .fieldset => "fieldset" | .legend => "legend" | .output => "output"
  | .p => "p" | .label => "label" | .table => "table" | .thead => "thead"
  | .tbody => "tbody" | .tr => "tr" | .th => "th" | .td => "td"

def attributePair : DisplayLayout.Attribute → String × String
  | .cssClass value => ("class", value)
  | .tabIndex value => ("tabindex", toString value)
  | .role value => ("role", value)
  | .ariaLabel value => ("aria-label", value)
  | .scope value => ("scope", value)
  | .colSpan value => ("colspan", toString value)

def layoutToJson : DisplayLayout.Node → Json
  | .hidden => .null
  | .control c => controlToJson c
  | .element tag attributes text children messages => Json.mkObj
      ([("kind", toJson "element"), ("tag", toJson (tagName tag)),
        ("attributes", toJson (attributes.map fun attr => let (name, value) := attributePair attr; toJson [name, value])),
        ("children", toJson (children.map layoutToJson))] ++
        text.toList.map (fun value => ("text", toJson value)) ++ messageFields messages)

def viewToJson (view : View) : Json := layoutToJson (DisplayLayout.ofView view)

end Forms.Runtime.DisplayProtocol
