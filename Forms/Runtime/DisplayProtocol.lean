module

public import Forms.Runtime.DisplayLayout
public import Forms.Runtime.EditorPresentation
public import Forms.Runtime.FeedbackProtocol
public import Forms.Runtime.Wire

@[expose] public section

namespace Forms.Runtime.DisplayProtocol
open Lean Display

def controlKey (target : Target) : ControlKey :=
  ⟨(toJson target.indices).compress⟩

def messageFields (messages : Option String) : List (String × Json) :=
  messages.toList.map fun message => ("messages", toJson message)

def widgetName : Editor → String
  | .text _ => "textInput"
  | .natural _ => "naturalInput"
  | .checkbox _ => "checkbox"

def controlToJson (control : Control) : Json :=
  Json.mkObj ([
    ("key", toJson control.key.value), ("target", toJson control.target.indices),
    ("label", toJson control.label), ("disabled", toJson control.disabled),
    ("kind", toJson "editor"), ("location", FeedbackProtocol.locationToJson control.location),
    ("widget", toJson (widgetName control.input))] ++ messageFields control.messages)

def attributePair : DisplayLayout.Attribute → String × String
  | .hidden => ("hidden", "")
  | .ariaLive => ("aria-live", "polite")
  | .ariaBusy value => ("aria-busy", toString value)
  | .runtime => ("data-runtime", "compiled")
  | .cssClass value => ("class", value)
  | .role value => ("role", value)
  | .ariaLabel value => ("aria-label", value)
  | .id value => ("id", value.value)
  | .inputType value => ("type", match value with
      | .text => "text" | .checkbox => "checkbox")
  | .numeric => ("inputmode", "numeric")
  | .naturalPattern => ("pattern", "[0-9]+")
  | .required => ("required", "")
  | .noValidate => ("novalidate", "")
  | .disabled => ("disabled", "")
  | .invalid => ("aria-invalid", "true")
  | .describedBy id => ("aria-describedby", id.value)

def sourceFields : DisplayLayout.Source → String × Wire.DomArgument
  | .value id => (id.value, .value)
  | .checked id => (id.value, .checked)

def bindingToWire : DisplayLayout.Binding → Wire.Binding
  | .page command => ⟨.click, (match command with | .submit => .submit | .reset => .reset), "", "", .none⟩
  | .draft key id => ⟨.input, .draft, key.value, id.value, .value⟩
  | .change key source => let (id, argument) := sourceFields source; ⟨.change, .apply, key.value, id, argument⟩
  | .submit key source => let (id, argument) := sourceFields source; ⟨.submit, .apply, key.value, id, argument⟩

def layoutToWire : DisplayLayout.Node → Option Wire.DisplayView
  | .hidden => none
  | .element tag attributes text children behavior =>
    let (value, checked) := match behavior.input with
      | .none => (none, none)
      | .value value => (some value, none)
      | .checked checked => (none, some checked)
    some (.element tag (attributes.map attributePair) (children.map layoutToWire)
      (behavior.bindings.map bindingToWire) text value checked (behavior.focusKey.map (·.value)))

end Forms.Runtime.DisplayProtocol
