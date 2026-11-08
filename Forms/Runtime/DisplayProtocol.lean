module

public import Forms.Runtime.DisplayLayout
public import Forms.Runtime.EditorPresentation
public import Forms.Runtime.FeedbackProtocol
public import Forms.Runtime.Wire

@[expose] public section

namespace Forms.Runtime.DisplayProtocol
open Lean Display

def targetToJson (target : Target) : Json :=
  toJson (target.map fun step => match step with
    | .name name => toJson name
    | .index index => toJson index)

/-- Preserve the opaque browser key format independently of internal view structure. -/
def controlKey (target : Target) (id : String) (index : Option Nat) : ControlKey :=
  ⟨(toJson ([targetToJson target, toJson id] ++ index.toList.map toJson)).compress⟩

def messageFields (messages : Option String) : List (String × Json) :=
  messages.toList.map fun message => ("messages", toJson message)

def widgetName : Editor → String
  | .text _ => "textInput"
  | .natural _ => "naturalInput"
  | .checkbox _ => "checkbox"

def controlToJson (control : Control) : Json :=
  let fields := match control.body with
    | .editor location input => [("kind", toJson "editor"),
        ("location", FeedbackProtocol.locationToJson location),
        ("widget", toJson (widgetName input))]
  Json.mkObj ([("key", toJson control.key.value), ("id", toJson control.id), ("target", targetToJson control.target),
    ("label", toJson control.label), ("disabled", toJson control.disabled)] ++ fields ++ messageFields control.messages)

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

def layoutToJson (node : DisplayLayout.Node) : Json := toJson (layoutToWire node)

def viewToJson (view : View) (state : Interaction.State := {}) : Json := layoutToJson (DisplayLayout.ofView state view)

end Forms.Runtime.DisplayProtocol
