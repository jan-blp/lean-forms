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

def Display.Commit.toReact : Commit → FormsReact.Commit
  | .onLeave => .onLeave
  | .whileTyping => .whileTyping

def _root_.Forms.Model.ReportMessage.texts
  (keep : Model.Diagnostic.ReportKind → Bool)
  (reports : List Model.ReportMessage)
  : List String :=
  (reports.filter (keep ·.kind)).map (·.text)

def _root_.FormsReact.Checks.of (reports : List Model.ReportMessage) : Option FormsReact.Checks :=
  let texts (keep : Model.Diagnostic.ReportKind → Bool) := Model.ReportMessage.texts keep reports
  let warnings (keep : Model.Diagnostic.ReportKind → Bool) :=
    texts fun kind => kind.severity == .warning && keep kind
  let unresolved := warnings fun kind => kind.state == .unresolved && !kind.outdated
  let outdated := warnings (·.outdated)
  let resolved (how : Model.Diagnostic.Resolution) :=
    warnings fun kind => kind.state == .resolved how && !kind.outdated
  let infos (outdated : Bool) :=
    texts fun kind => kind.severity == .info && kind.outdated == outdated
  let tone : FormsReact.Tone :=
    if !unresolved.isEmpty then .attention
    else if !outdated.isEmpty then .outdated
    else if !(resolved .passed).isEmpty || !(resolved .approved).isEmpty then .resolved
    else .info
  if unresolved.isEmpty && outdated.isEmpty && (resolved .passed).isEmpty &&
    (resolved .approved).isEmpty && (infos false).isEmpty && (infos true).isEmpty then none
  else some
    { tone
      unresolved
      outdated
      resolved := resolved .passed
      approved := resolved .approved
      info := infos false
      outdatedInfo := infos true }

theorem _root_.FormsReact.Checks.of_attention
  {reports : List Model.ReportMessage}
  {grouped : FormsReact.Checks}
  (built : FormsReact.Checks.of reports = some grouped)
  : grouped.tone = .attention ↔ grouped.unresolved ≠ [] := by
  simp only [FormsReact.Checks.of] at built
  split at built
  · cases built
  · cases built
    repeat' split
    all_goals simp_all

theorem _root_.FormsReact.Checks.of_resolved
  {reports : List Model.ReportMessage}
  {grouped : FormsReact.Checks}
  (built : FormsReact.Checks.of reports = some grouped)
  : grouped.tone = .resolved ↔
    grouped.unresolved = [] ∧ grouped.outdated = [] ∧
      (grouped.resolved ≠ [] ∨ grouped.approved ≠ []) := by
  simp only [FormsReact.Checks.of] at built
  split at built
  · cases built
  · cases built
    repeat' split
    all_goals simp_all

theorem _root_.FormsReact.Checks.of_info
  {reports : List Model.ReportMessage}
  {grouped : FormsReact.Checks}
  (built : FormsReact.Checks.of reports = some grouped)
  : grouped.tone = .info ↔
    grouped.unresolved = [] ∧ grouped.outdated = [] ∧ grouped.resolved = [] ∧
      grouped.approved = [] := by
  simp only [FormsReact.Checks.of] at built
  split at built
  · cases built
  · cases built
    repeat' split
    all_goals simp_all [Decidable.or_iff_not_imp_left]

def Display.Evidence.toReact : Evidence → FormsReact.Evidence
  | .unsupported => .unsupported
  | .missing => .missing
  | .linked evidence stale => .linked evidence.page evidence.cellIds stale

def Display.SearchResults.toReact : SearchResults → FormsReact.SearchResults
  | .loading => .loading
  | .failed message => .failed message
  | .found options more =>
    .found (options.map fun option => {
      value := option.value, label := option.label, disabledReason := option.disabledReason }) more

def Display.Control.toReact (pending : Bool) (c : Control) : FormsReact.Component :=
  let name := ControlKeyProtocol.toString c.key
  let disabled := pending || c.disabled
  match c.input with
  | .field (.text kind value commit) evidence => .textField {
      name
      label := c.label
      kind := kind.toReact
      value
      commit := commit.toReact
      disabled
      errors := Model.Message.errors c.messages
      evidence := evidence.toReact
      onCommit := .apply name }
  | .field (.checkbox checked) evidence => .checkbox {
      name
      label := c.label
      checked
      disabled
      errors := Model.Message.errors c.messages
      evidence := evidence.toReact
      onChange := .apply name }
  | .choice value options => .choice {
      name
      label := c.label
      value
      options := options.map fun option => {
        value := option.value, label := option.label, disabledReason := option.disabledReason }
      disabled
      errors := Model.Message.errors c.messages
      onChange := .apply name }
  | .field (.choices values options) evidence => .choices {
      name
      label := c.label
      values
      options := options.map fun option => { value := option.value, label := option.label }
      disabled
      errors := Model.Message.errors c.messages
      evidence := evidence.toReact
      onChange := .apply name }
  | .lookup picked search => .lookup {
      name
      label := c.label
      picked := picked.map fun option => { value := option.value, label := option.label }
      search := search.map fun { text, results } => { text, results := results.toReact }
      disabled
      errors := Model.Message.errors c.messages
      onChange := .apply name }
  | .action => .button { label := c.label, variant := .secondary, disabled, onClick := .press name }
  | .tabs active labels =>
    .tabBar { name, label := c.label, active, labels, disabled, onChange := .apply name }
  | .hostWidget contract input => .hostWidget {
      name, contract, input, disabled
      label := c.label
      errors := Model.Message.errors c.messages
      onChange := .apply name }

/-- A group with no label or messages. -/
def plainGroup
  (key : Option String)
  (children : List FormsReact.Component)
  : FormsReact.Component :=
  .group { label := none, children, errors := [], key }

mutual
def Display.View.toReact (pending : Bool) : View → Option FormsReact.Component
  | .hidden => none
  | .control c => some (c.toReact pending)
  | .stack label children => some (.group {
      label := label.filter (!·.isEmpty)
      children := children.filterMap (·.toReact pending)
      errors := []
      key := none })
  | .list label children messages => some (.group {
      label := some label
      children := children.filterMap (·.toReact pending)
      errors := Model.Message.errors messages
      key := none })
  | .keyed key body => (body.toReact pending).map fun component => match component with
    | .group group => .group { group with key := some key.value }
    | .textField _
    | .checkbox _
    | .choice _
    | .choices _
    | .lookup _
    | .output _
    | .button _
    | .tabBar _
    | .hostWidget _
    | .table _
    | .page _
    | .statusMarker _ => plainGroup (some key.value) [component]
  | .computed label value => some (.output { label, value })
  | .marker reports => (FormsReact.Checks.of reports).map .statusMarker
  | .table label headers rows footer messages => some (.table {
      label, headers
      rows := tableRowsToReact pending rows
      footer := (footer.toReact pending).getD (plainGroup none [])
      errors := Model.Message.errors messages })

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
