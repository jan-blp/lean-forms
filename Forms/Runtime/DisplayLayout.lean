module

public import Forms.Runtime.EditorPresentation
public import Forms.Runtime.Interaction

@[expose] public section

namespace Forms.Runtime.DisplayLayout
open Display

inductive Tag where
  | header | span | h1 | section | details | summary | pre
  | div | fieldset | legend | output | p | label
  | input | button | form

inductive InputType where
  | text | checkbox

inductive Attribute where
  | hidden
  | ariaLive
  | ariaBusy (value : Bool)
  | runtime
  | cssClass (value : String)
  | role (value : String)
  | ariaLabel (value : String)
  | id (value : DomId)
  | inputType (value : InputType)
  | numeric
  | naturalPattern
  | required
  | disabled
  | invalid
  | describedBy (id : DomId)

inductive Source where
  | value (id : DomId)
  | checked (id : DomId)

inductive PageCommand where
  | submit | reset

inductive Binding where
  | page (command : PageCommand)
  | draft (key : ControlKey) (source : DomId)
  | change (key : ControlKey) (source : Source)
  | submit (key : ControlKey) (source : Source)

inductive InputValue where
  | none
  | value (text : String)
  | checked (value : Bool)

structure Behavior where
  input : InputValue := .none
  focusKey : Option ControlKey := none
  bindings : List Binding := []

inductive Node where
  | hidden
  | element (tag : Tag) (attributes : List Attribute) (text : Option String)
      (children : List Node) (behavior : Behavior)

def element (tag : Tag) (children : List Node := []) (attributes : List Attribute := [])
    (text : Option String := none) (messages : Option String := none) (behavior : Behavior := {}) : Node :=
  let feedback := messages.toList.map fun message =>
    Node.element .p [.cssClass "validation-error"] (some message) [] {}
  .element tag attributes text (children ++ feedback) behavior

def text (tag : Tag) (value : String) (attributes : List Attribute := []) : Node :=
  element tag [] attributes (some value)

def control (state : Interaction.State) (c : Control) : Node := Id.run do
  let disabled := state.pending || c.disabled
  let attrs := if disabled then [Attribute.disabled] else []
  let token := String.intercalate "-" (c.key.value.toUTF8.toList.map fun byte => toString byte.toNat)
  let inputId := DomId.mk ("input-" ++ token)
  let feedbackId := DomId.mk ("feedback-" ++ token)
  let feedback := c.messages.toList.map fun message => text .p message [.cssClass "validation-error", .id feedbackId]
  let inputAttrs := [.id inputId] ++ attrs ++ if c.messages.isSome then [.invalid, .describedBy feedbackId] else []
  let (input, argument, applyButton) := match EditorPresentation.ofEditor c.input with
    | .onApply draft =>
      let constraints := match draft with
        | .text _ => [Attribute.inputType .text]
        | .natural _ => [.inputType .text, .numeric, .naturalPattern, .required]
      let value := (state.drafts.find? (·.1 == c.key)).map Prod.snd |>.getD draft.value
      (element .input [] (constraints ++ inputAttrs)
        (behavior := { input := .value value, focusKey := some c.key, bindings := if disabled then [] else [.draft c.key inputId] }), Source.value inputId,
        [element .button [] attrs (some "Apply")])
    | .onChange checked =>
      (element .input [] (.inputType .checkbox :: inputAttrs)
        (behavior := { input := .checked checked, focusKey := some c.key, bindings := [.change c.key (.checked inputId)] }),
        Source.checked inputId, [])
  return element .form (element .label [input] (text := some c.label) :: applyButton ++ feedback) [.cssClass "editor"]
    (behavior := { bindings := [.submit c.key argument] })

def group (label : String) (children : List Node) (messages : Option String := none) : Node :=
  if label.isEmpty then element .div children [.cssClass "stack"] (messages := messages)
  else element .fieldset (text .legend label :: children) [.cssClass "component"] (messages := messages)

def ofView (state : Interaction.State := {}) : View → Node
  | .hidden => .hidden
  | .control c => control state c
  | .stack label children => group (label.getD "") (children.map (ofView state))
  | .computed label value => element .div
      [element .label [text .output value] (text := some label)] [.cssClass "computed"]

def page (view : View) (state : Interaction.State) (count : Nat) (result : String) : Node :=
  let disabled := if state.pending then [Attribute.disabled] else []
  element .div [
    element .header [text .span "LEAN FORMS" [.cssClass "brand"]],
    text .h1 view.title [.id ⟨"title"⟩],
    element .section [ofView state view]
      [.id ⟨"controls"⟩, .ariaLabel "Form controls", .ariaBusy state.pending, .runtime],
    element .div [
      element .button [] ([.id ⟨"submit"⟩, .cssClass "primary"] ++ disabled) (some "Submit")
        (behavior := { bindings := [.page .submit] }),
      element .button [] ([.id ⟨"reset"⟩] ++ disabled) (some "Start over")
        (behavior := { bindings := [.page .reset] }),
      text .span (s!"{count} " ++ if count == 1 then "action" else "actions") [.id ⟨"count"⟩]
    ] [.cssClass "toolbar"],
    text .p state.status ([.id ⟨"status"⟩, .role "status", .ariaLive] ++
      if state.error then [.cssClass "error"] else []),
    element .details [text .summary "Submitted value", text .pre (if state.resultVisible then result else "")]
      ([.id ⟨"result"⟩] ++ if state.resultVisible then [] else [.hidden])
  ]

end Forms.Runtime.DisplayLayout
