module

public import Forms.Runtime.DisplayLayout
public import Forms.Runtime.EditorPresentation
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

def widgetName : Editor → String
  | .text _ => "textInput"
  | .natural _ => "naturalInput"
  | .date _ => "dateInput"
  | .checkbox _ => "checkbox"
  | .select .. => "select"

def controlToJson (control : Control) : Json :=
  let fields := match control.body with
    | .button keepDrafts => [("kind", toJson "button"), ("keepDrafts", toJson keepDrafts)]
    | .editor location input => [("kind", toJson "editor"),
        ("location", FeedbackProtocol.locationToJson location),
        ("widget", toJson (widgetName input))] ++
        (match input with | .select _ options => [("options", toJson options)] | _ => [])
    | .choice location value options => [("kind", toJson "choice"),
        ("location", FeedbackProtocol.locationToJson location), ("value", toJson value), ("options", toJson options)]
  Json.mkObj ([("key", toJson control.key), ("id", toJson control.id), ("target", targetToJson control.target),
    ("label", toJson control.label), ("disabled", toJson control.disabled)] ++ fields ++ messageFields control.messages)

def tagName : DisplayLayout.Tag → String
  | .div => "div" | .fieldset => "fieldset" | .legend => "legend" | .output => "output"
  | .p => "p" | .label => "label" | .table => "table" | .thead => "thead"
  | .tbody => "tbody" | .tr => "tr" | .th => "th" | .td => "td"
  | .input => "input" | .select => "select" | .option => "option" | .button => "button" | .form => "form"

def attributePair : DisplayLayout.Attribute → String × String
  | .cssClass value => ("class", value)
  | .tabIndex value => ("tabindex", toString value)
  | .role value => ("role", value)
  | .ariaLabel value => ("aria-label", value)
  | .scope value => ("scope", value)
  | .colSpan value => ("colspan", toString value)
  | .id value => ("id", value)
  | .inputType value => ("type", match value with
      | .text => "text" | .date => "date" | .checkbox => "checkbox" | .button => "button" | .submit => "submit")
  | .numeric => ("inputmode", "numeric")
  | .naturalPattern => ("pattern", "[0-9]+")
  | .required => ("required", "")
  | .minDate => ("min", "0001-01-01")
  | .maxDate => ("max", "9999-12-31")
  | .disabled => ("disabled", "")
  | .optionValue value => ("value", value)
  | .invalid => ("aria-invalid", "true")
  | .describedBy id => ("aria-describedby", id)

def sourceFields : DisplayLayout.Source → List (String × Json)
  | .value id => [("source", toJson id), ("argument", toJson "value")]
  | .checked id => [("source", toJson id), ("argument", toJson "checked")]
  | .index id => [("source", toJson id), ("argument", toJson "index")]

def bindingToJson (binding : DisplayLayout.Binding) : Json :=
  let (event, command, key, fields) := match binding with
    | .press key => ("click", "apply", key, [("source", toJson ""), ("argument", toJson "none")])
    | .draft key id => ("input", "draft", key, sourceFields (.value id))
    | .change key source => ("change", "apply", key, sourceFields source)
    | .submit key source => ("submit", "apply", key, sourceFields source)
  Json.mkObj ([("event", toJson event), ("command", toJson command), ("key", toJson key)] ++ fields)

def inputFields : DisplayLayout.InputValue → List (String × Json)
  | .none => []
  | .value text => [("value", toJson text)]
  | .checked value => [("checked", toJson value)]

def layoutToJson : DisplayLayout.Node → Json
  | .hidden => .null
  | .element tag attributes text children behavior => Json.mkObj
      ([("kind", toJson "element"), ("tag", toJson (tagName tag)),
        ("attributes", toJson (attributes.map fun attr => let (name, value) := attributePair attr; toJson [name, value])),
        ("children", toJson (children.map layoutToJson)), ("bindings", toJson (behavior.bindings.map bindingToJson))] ++
        text.toList.map (fun value => ("text", toJson value)) ++
        inputFields behavior.input ++
        behavior.focusKey.toList.map (fun value => ("focusKey", toJson value)))

def viewToJson (view : View) (state : Interaction.State := {}) : Json := layoutToJson (DisplayLayout.ofView state view)

end Forms.Runtime.DisplayProtocol
