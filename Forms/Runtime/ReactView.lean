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

def _root_.Forms.Model.TextKind.toReact : Model.TextKind → FormsReact.TextKind
  | .plain => .plain
  | .natural => .natural
  | .integer => .integer
  | .decimal => .decimal
  | .date => .date
  | .uuid => .uuid

def Display.Control.toReact (pending : Bool) (c : Control) : FormsReact.Component :=
  let name := ControlKeyProtocol.toString c.key
  let disabled := pending || c.disabled
  match c.input with
  | .text kind value => .textField {
      name
      label := c.label
      kind := kind.toReact
      value
      disabled
      errors := Model.Message.texts .error c.messages
      reports := Model.Message.texts .report c.messages
      onCommit := .apply name }
  | .checkbox checked => .checkbox {
      name
      label := c.label
      checked
      disabled
      errors := Model.Message.texts .error c.messages
      reports := Model.Message.texts .report c.messages
      onChange := .apply name }
  | .choice value options => .choice {
      name
      label := c.label
      value
      options := options.map fun option => { value := option.value, label := option.label }
      disabled
      errors := Model.Message.texts .error c.messages
      reports := Model.Message.texts .report c.messages
      onChange := .apply name }
  | .choices values options => .choices {
      name
      label := c.label
      values
      options := options.map fun option => { value := option.value, label := option.label }
      disabled
      errors := Model.Message.texts .error c.messages
      reports := Model.Message.texts .report c.messages
      onChange := .apply name }
  | .action => .button { label := c.label, variant := .secondary, disabled, onClick := .press name }
  | .tabs active labels =>
    .tabBar { name, label := c.label, active, labels, disabled, onChange := .apply name }

/-- A group with no label or messages. -/
def plainGroup
  (key : Option String)
  (children : List FormsReact.Component)
  : FormsReact.Component :=
  .group { label := none, children, errors := [], reports := [], key }

mutual
def Display.View.toReact (pending : Bool) : View → Option FormsReact.Component
  | .hidden => none
  | .control c => some (c.toReact pending)
  | .stack label children => some (.group {
      label := label.filter (!·.isEmpty)
      children := children.filterMap (·.toReact pending)
      errors := []
      reports := []
      key := none })
  | .list label children messages => some (.group {
      label := some label
      children := children.filterMap (·.toReact pending)
      errors := Model.Message.texts .error messages
      reports := Model.Message.texts .report messages
      key := none })
  | .keyed key body => (body.toReact pending).map fun component => match component with
    | .group group => .group { group with key := some key.value }
    | .textField _
    | .checkbox _
    | .choice _
    | .choices _
    | .output _
    | .button _
    | .tabBar _
    | .table _
    | .page _ => plainGroup (some key.value) [component]
  | .computed label value => some (.output { label, value })
  | .table label headers rows footer messages => some (.table {
      label, headers
      rows := tableRowsToReact pending rows
      footer := (footer.toReact pending).getD (plainGroup none [])
      errors := Model.Message.texts .error messages
      reports := Model.Message.texts .report messages })

def tableRowsToReact (pending : Bool) : List Display.TableRow → List FormsReact.TableRow
  | [] => []
  | ⟨key, label, cells, selected⟩ :: rest =>
    { key := key.value, label, selected, cells := tableCellsToReact pending cells } ::
      tableRowsToReact pending rest

/-- Hidden cells stay empty so later cells keep their column. -/
def tableCellsToReact (pending : Bool) : List View → List FormsReact.Component
  | [] => []
  | cell :: rest =>
    (cell.toReact pending).getD (plainGroup none []) :: tableCellsToReact pending rest
end

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
