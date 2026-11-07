module

public import Forms.Runtime.EditorPresentation
public import Forms.Runtime.Interaction

@[expose] public section

namespace Forms.Runtime.DisplayLayout
open Display

inductive Tag where
  | div | fieldset | legend | output | p | label
  | table | thead | tbody | tr | th | td
  | input | select | option | button | form

inductive InputType where
  | text | date | checkbox | button | submit

inductive Attribute where
  | cssClass (value : String)
  | tabIndex (value : Nat)
  | role (value : String)
  | ariaLabel (value : String)
  | scope (value : String)
  | colSpan (value : Nat)
  | id (value : String)
  | inputType (value : InputType)
  | numeric
  | naturalPattern
  | required
  | minDate | maxDate
  | disabled
  | optionValue (value : String)
  | invalid
  | describedBy (id : String)

inductive Source where
  | value (id : String)
  | checked (id : String)
  | index (id : String)

inductive Binding where
  | press (key : String)
  | draft (key source : String)
  | change (key : String) (source : Source)
  | submit (key : String) (source : Source)

inductive InputValue where
  | none
  | value (text : String)
  | checked (value : Bool)

structure Behavior where
  input : InputValue := .none
  focusKey : Option String := none
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
  let token := String.intercalate "-" (c.key.toUTF8.toList.map fun byte => toString byte.toNat)
  let inputId := "input-" ++ token
  let feedbackId := "feedback-" ++ token
  let feedback := c.messages.toList.map fun message => text .p message [.cssClass "validation-error", .id feedbackId]
  let inputAttrs := [.id inputId] ++ attrs ++ if c.messages.isSome then [.invalid, .describedBy feedbackId] else []
  let select (value : String) (options : List (String × String)) (source : Source) :=
    element .select (options.map fun (value, label) => text .option label [.optionValue value]) inputAttrs
      (behavior := { input := .value value, focusKey := some c.key, bindings := [.change c.key source] })
  match c.body with
  | .button _ =>
    return element .button [] ([.cssClass "action", .inputType .button] ++ attrs) (some c.label)
      (behavior := { focusKey := some c.key, bindings := [.press c.key] })
  | .choice _ value options =>
    return element .label
      (select value (options.map fun name => (name, name)) (.value inputId) :: feedback) [.cssClass "choice"] (some c.label)
  | .editor _ editor =>
    let (input, argument, applyButton) := match EditorPresentation.ofEditor editor with
      | .onApply draft =>
        let constraints := match draft with
          | .text _ => [Attribute.inputType .text]
          | .natural _ => [.inputType .text, .numeric, .naturalPattern, .required]
          | .date _ => [.inputType .date, .minDate, .maxDate, .required]
        let value := (state.drafts.find? (·.1 == c.key)).map Prod.snd |>.getD draft.value
        (element .input [] (constraints ++ inputAttrs)
          (behavior := { input := .value value, focusKey := some c.key, bindings := if disabled then [] else [.draft c.key inputId] }), Source.value inputId,
          [element .button [] attrs (some "Apply")])
      | .onChange (.checkbox checked) =>
        (element .input [] (.inputType .checkbox :: inputAttrs)
          (behavior := { input := .checked checked, focusKey := some c.key, bindings := [.change c.key (.checked inputId)] }),
          Source.checked inputId, [])
      | .onChange (.select selected options) =>
        (select (toString selected) (options.zipIdx.map fun (label, index) => (toString index, label)) (.index inputId),
          Source.index inputId, [])
    return element .form (element .label [input] (text := some c.label) :: applyButton ++ feedback) [.cssClass "editor"]
      (behavior := { bindings := [.submit c.key argument] })

def group (label : String) (children : List Node) (messages : Option String := none) : Node :=
  if label.isEmpty then element .div children [.cssClass "stack"] (messages := messages)
  else element .fieldset (text .legend label :: children) [.cssClass "component"] (messages := messages)

def ofView (state : Interaction.State := {}) : View → Node
  | .hidden => .hidden
  | .control c => control state c
  | .stack label children => group (label.getD "") (children.map (ofView state))
  | .actionWidget label value _ children messages =>
      group label (text .output value [.cssClass "value"] :: children.map (control state)) messages
  | .list label _ items append messages =>
      let bodies := items.map fun item => (ofView state item.1, item.2)
      let rows := bodies.zipIdx.map fun (item, index) =>
        element .fieldset [text .legend s!"Item {index + 1}", item.1, control state item.2] [.cssClass "list-item"]
      element .fieldset
        (text .legend label :: (if items.isEmpty then [text .p "No items." [.cssClass "empty"]] else rows) ++ [control state append])
        [.cssClass "component"] (messages := messages)
  | .sum selector body => element .div [control state selector, ofView state body] [.cssClass "sum"]
  | .computed label value => element .div
      [element .label [text .output value] (text := some label)] [.cssClass "computed"]
  | .text value => text .p value [.cssClass "text"]
  | .table columns rows =>
      let head := element .thead [element .tr (columns.map fun title => text .th title [.scope "col"])]
      let body := if rows.isEmpty && !columns.isEmpty then
          [element .tr [text .td "No rows." [.cssClass "empty", .colSpan columns.length]]]
        else rows.map fun cells => element .tr (cells.map (text .td ·))
      element .div [element .table [head, element .tbody body]]
        [.cssClass "table-scroll", .tabIndex 0, .role "region", .ariaLabel "Table"]
termination_by view => sizeOf view
decreasing_by
  all_goals first
    | decreasing_trivial
    | have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
      have hp : sizeOf item.1 < sizeOf item := by cases item; simp +arith
      simp_wf
      omega

end Forms.Runtime.DisplayLayout
