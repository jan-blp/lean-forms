module

public import FormsReact.Component
public import Forms.Runtime.Display
public import Forms.Runtime.ControlKeyProtocol
public import Forms.Runtime.Interaction

@[expose] public section
namespace Forms.Runtime
open Display

def Interaction.Notice.toReact : Interaction.Notice → FormsReact.Notice
  | .info message => .info message
  | .error message => .error message

def Display.Control.toReact (pending : Bool) (c : Control) : FormsReact.Component :=
  let name := ControlKeyProtocol.toString c.key
  let disabled := pending || c.disabled
  match c.input with
  | .text value => .textField
      { name, label := c.label, value, disabled, error := c.messages, onCommit := .apply name }
  | .natural value => .naturalField
      { name, label := c.label, value := toString value, disabled, error := c.messages, onCommit := .apply name }
  | .checkbox checked => .checkbox
      { name, label := c.label, checked, disabled, error := c.messages, onChange := .apply name }
  | .choice value options => .choice {
      name
      label := c.label
      value
      options := options.map fun option => { value := option.value, label := option.label }
      disabled
      error := c.messages
      onChange := .apply name }
  | .action => .button { label := c.label, variant := .secondary, disabled, onClick := .press name }
  | .tabs active labels =>
    .tabBar { name, label := c.label, active, labels, disabled, onChange := .apply name }

mutual
def Display.View.toReact (pending : Bool) : View → Option FormsReact.Component
  | .hidden => none
  | .control c => some (c.toReact pending)
  | .stack label children => some (.group
      { label := label.filter (!·.isEmpty), children := children.filterMap (·.toReact pending), error := none })
  | .list label children messages => some (.group
      { label := some label, children := children.filterMap (·.toReact pending), error := messages })
  | .computed label value => some (.output { label, value })
  | .table label headers rows footer messages => some (.table {
      label, headers
      rows := tableRowsToReact pending rows
      footer := (footer.toReact pending).getD (.group { label := none, children := [], error := none })
      error := messages })

def tableRowsToReact (pending : Bool) : List Display.TableRow → List FormsReact.TableRow
  | [] => []
  | ⟨label, cells, selected⟩ :: rest =>
    { label, selected, cells := tableCellsToReact pending cells } :: tableRowsToReact pending rest

/-- Hidden cells stay empty so later cells keep their column. -/
def tableCellsToReact (pending : Bool) : List View → List FormsReact.Component
  | [] => []
  | cell :: rest =>
    ((cell.toReact pending).getD (.group { label := none, children := [], error := none })) ::
      tableCellsToReact pending rest
end

/-- The whole page: `view` plus toolbar, notice and submitted `result`. -/
def Display.View.toReactPage
  (view : View)
  (state : Interaction.State)
  (result : String)
  : FormsReact.Component :=
  .page {
    title := view.title
    busy := state.pending
    body := (view.toReact state.pending).toList
    toolbar := [
      .button { label := "Submit", variant := .primary, disabled := state.pending, onClick := .submit },
      .button { label := "Start over", variant := .secondary, disabled := state.pending, onClick := .reset }]
    notice := state.notice.toReact
    result := if state.resultVisible then some result else none }

end Forms.Runtime
