module

public import Forms.Runtime.Display

@[expose] public section

namespace Forms.Runtime.DisplayLayout
open Display

/-- Static layout uses a closed set of tags and attributes; controls retain browser event bindings. -/
inductive Tag where
  | div | fieldset | legend | output | p | label
  | table | thead | tbody | tr | th | td

inductive Attribute where
  | cssClass (value : String)
  | tabIndex (value : Nat)
  | role (value : String)
  | ariaLabel (value : String)
  | scope (value : String)
  | colSpan (value : Nat)

inductive Node where
  | hidden
  | control (value : Control)
  | element (tag : Tag) (attributes : List Attribute) (text : Option String)
      (children : List Node) (messages : Option String)

def element (tag : Tag) (children : List Node := []) (attributes : List Attribute := [])
    (text : Option String := none) (messages : Option String := none) : Node :=
  .element tag attributes text children messages

def text (tag : Tag) (value : String) (attributes : List Attribute := []) : Node :=
  element tag [] attributes (some value)

def group (label : String) (children : List Node) (messages : Option String := none) : Node :=
  if label.isEmpty then element .div children [.cssClass "stack"] (messages := messages)
  else element .fieldset (text .legend label :: children) [.cssClass "component"] (messages := messages)

def ofView : View → Node
  | .hidden => .hidden
  | .control c => .control c
  | .stack label children => group (label.getD "") (children.map ofView)
  | .actionWidget label value _ children messages =>
      group label (text .output value [.cssClass "value"] :: children.map Node.control) messages
  | .list label _ items append messages =>
      let bodies := items.map fun item => (ofView item.1, item.2)
      let rows := bodies.zipIdx.map fun (item, index) =>
        element .fieldset [text .legend s!"Item {index + 1}", item.1, .control item.2] [.cssClass "list-item"]
      element .fieldset
        (text .legend label :: (if items.isEmpty then [text .p "No items." [.cssClass "empty"]] else rows) ++ [.control append])
        [.cssClass "component"] (messages := messages)
  | .sum selector body => element .div [.control selector, ofView body] [.cssClass "sum"]
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
