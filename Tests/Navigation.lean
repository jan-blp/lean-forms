module

public import Forms.ExampleForms.Navigation
public import Forms.ExampleForms.Expenses
public import Forms.Runtime.ModelForm
public import Tests.FreshId

public section
namespace Tests.Navigation
open Forms.Model Forms.Runtime Forms.ExampleForms

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

private def opened
  {β : Type}
  (form : Component [] Person.Raw β)
  (value : Person.Raw)
  : ModelForm.State form :=
  ModelForm.openState (model := Person) (supply := supply) form value Env.nil

private def apply
  {β : Type}
  (form : Component [] Person.Raw β)
  (state : ModelForm.State form)
  (label : String)
  (input : Option Input := none)
  : IO (ModelForm.State form) := do
  let some control := state.evaluation.view.controls.find? (·.label == label)
    | throw (IO.userError s!"Missing control: {label}")
  IO.ofExcept (ModelForm.execute (model := Person) form state (.apply control.key input))

private def focuses
  {Γ : Context}
  {α β : Type}
  {form : Component Γ α β}
  (state : ModelForm.State form)
  : List ControlKey :=
  state.outbox.filterMap fun
    | .focus key => some key
    | .submit => none
    | .fetch _ => none

private def remembered : Component [] Person.Raw :=
  .bind (none : Option Destination) <|
    .observe .issues <|
      let saved : Var _ (Option Destination) := .there .here
      let first : Computation _ Person.Raw (Option Destination) := {
        inputs := inputs[.ui (Ref.here : InputRef _ (List Issue))]
        run := fun issues => issues.head?.bind (·.destination?) }
      .group "Remembered destinations" [
        .field path[Person.Field.name] "Name" .text,
        .button "Remember" (.set saved first),
        .button "Visit saved" (.visit { inputs := inputs[.ui saved], run := id }),
        .button "Visit current" (.visit first)]

private def rememberedRow : Component [] ExpenseReport.Raw :=
  .bind (none : Option Destination) <|
    .observe .issues <|
      let saved : Var _ (Option Destination) := .there .here
      .group "Remembered row" [
        ExpenseReport.listForm,
        .button "Remember" (.set saved {
          inputs := inputs[.ui (Ref.here : InputRef _ (List Issue))]
          run := fun issues => issues.head?.bind (·.destination?) }),
        .button "Visit saved" (.visit { inputs := inputs[.ui saved], run := id })]

private def press
  (form : Component [] ExpenseReport.Raw)
  (state : ModelForm.State form)
  (label : String)
  : IO (ModelForm.State form) := do
  let some control := state.evaluation.view.controls.find? (·.label == label)
    | throw (IO.userError s!"Missing control: {label}")
  IO.ofExcept (ModelForm.execute (model := ExpenseReport) form state (.apply control.key none))

def run : IO Unit := do
  let name : ErasedLocation := [.field "name"]
  let street : ErasedLocation := [.field "address", .field "street"]
  let diagnostics : List Diagnostic := [
    { kind := .error, message := "Both", targets := .locations name [street] },
    { kind := .error, message := "Global", targets := .global }]
  let root := Component.issues.evaluate Person.initial Env.nil (diagnostics := diagnostics)
  let address : Component [] Person.Raw (Option (List Issue)) :=
    .zoom? (.const (some (.ofPath path[Person.Field.address]))) .issues
  let addressIssues :=
    (address.evaluate Person.initial Env.nil (diagnostics := diagnostics)).output.getD []
  check "IssuesAreOrdinaryScopedOutput"
    (root.output.length == 2 && addressIssues.map (·.message) == ["Both"] &&
      addressIssues.head?.bind (·.destination?) == some { locations := [street] })

  let rows : Component [] (Collection Address.Raw) (List (List Issue)) :=
    .list .self "Addresses" (.numbered "Address") "Add" ⟨""⟩ .issues
  let secondStreet : ErasedLocation := [.item secondId, .field "street"]
  let rowIssues : List Diagnostic := [
    { kind := .error, message := "Second address", targets := .locations secondStreet [] }]
  let collected := (rows.evaluate (.numbered [⟨"Main"⟩, ⟨""⟩]) Env.nil
    (diagnostics := rowIssues)).output
  check "CollectionsCollectIssueOutputs"
    (collected.map List.length == [0, 1] &&
      (collected[1]?.getD []).head?.bind (·.destination?) == some { locations := [secondStreet] })

  let form := Forms.ExampleForms.Navigation.form
  let initial := opened form Forms.ExampleForms.Navigation.initial
  check "UnplacedPaneStillExportsIssues"
    (initial.evaluation.output.length == 1 &&
      !(initial.evaluation.view.controls.any (·.label == "Street")))
  let visited ← apply form initial "Go to address problem"
  check "VisitResolvesAfterTabChange"
    (visited.evaluation.output.length == 1 &&
      visited.evaluation.view.controls.any (·.label == "Street") &&
      focuses visited == [.edit street])
  let edited ← apply form visited "Street" (some (.text "Main"))
  check "IssueOutputsRefreshAfterEdit"
    (edited.evaluation.output.isEmpty && edited.evaluation.view.controls.any
      (fun control => control.label == "Go to address problem" && control.disabled))
  let pending ← IO.ofExcept (ModelForm.execute (model := Person) form edited .submit)
  let rejected ← IO.ofExcept (ModelForm.execute (model := Person) form pending
    (.submitted (.rejected
      (.validation { message := "Server street", targets := .locations street [] } []))))
  check "ServerFeedbackRefreshesIssueOutputs"
    (rejected.evaluation.output.map (·.message) == ["Server street"] &&
      rejected.evaluation.view.controls.any
        (fun control => control.label == "Go to address problem" && !control.disabled))

  let numeric := opened form Person.initial
  let invalid ← apply form numeric "Age" (some (.text "abc"))
  check "RejectedDraftBecomesObservableIssue"
    (invalid.evaluation.output.map (·.message) == ["Enter a non-negative whole number."] &&
      invalid.evaluation.view.controls.any
        (fun control => control.label == "Age" && !control.messages.isEmpty))
  let corrected ← apply form invalid "Age" (some (.text "21"))
  check "SuccessfulCommitClearsDraftIssue" corrected.evaluation.output.isEmpty
  let browser ← IO.ofExcept (ModelForm.execute (model := Person) form numeric
    (.draft (.edit [.field "age"]) (some "Incomplete browser input")))
  let cleared ← IO.ofExcept (ModelForm.execute (model := Person) form browser
    (.draft (.edit [.field "age"]) none))
  check "BrowserDiagnosticsUseTheSameIssueOutput"
    (browser.evaluation.output.map (·.message) == ["Incomplete browser input"] &&
      cleared.evaluation.output.isEmpty && browser.value.age == numeric.value.age)
  let conditional : Component [] Person.Raw (List Issue) :=
    .observe .issues <| .withOutput Person.form {
      inputs := inputs[.ui (Ref.here : InputRef _ (List Issue))], run := id }
  let shown := opened conditional { Person.initial with delivery := true }
  let draft ← IO.ofExcept (ModelForm.execute (model := Person) conditional shown
    (.draft (.edit street) (some "Uncommitted street")))
  let hidden ← apply conditional draft "Request delivery" (some (.boolean false))
  check "RemovingAControlClearsItsDraftDiagnostic"
    (draft.evaluation.output.length == 1 && hidden.evaluation.output.isEmpty)

  let invalidName := opened remembered { Person.initial with name := "" }
  let saved ← apply remembered invalidName "Remember"
  let later ← apply remembered saved "Visit saved"
  let fresh ← apply remembered later "Visit current"
  check "SavedDestinationsStayValid"
    (focuses later == [.edit name] && focuses fresh == [.edit name])
  let acknowledged ← IO.ofExcept
    (ModelForm.execute (model := Person) remembered fresh (.submitted (.accepted fresh.value)))
  check "FocusIsAnEventEffect" (focuses acknowledged).isEmpty

  let report : ExpenseReport.Raw := { ExpenseReport.initial with
    expenses := .numbered [⟨"Train to Bern", 58, false⟩, ⟨"", 180, true⟩] }
  let rowsOpened := ModelForm.openState (model := ExpenseReport) (supply := supply) rememberedRow
    report Env.nil
  let rowSaved ← press rememberedRow rowsOpened "Remember"
  let rowRemoved ← press rememberedRow rowSaved "Remove"
  let rowVisited ← press rememberedRow rowRemoved "Visit saved"
  check "SavedDestinationFollowsItsRowAfterRemoval"
    (rowRemoved.value.expenses.length == 1 &&
      focuses rowVisited == [.edit [.field "expenses", .item secondId, .field "description"]])

  let fields : Component [] Person.Raw := .group "Fields" [
    .disabledWhen (.const true) (.field path[Person.Field.name] "Name" .text),
    .field path[Person.Field.age] "Age" .natural]
  let view := (fields.evaluate Person.initial Env.nil).view
  check "ResolutionSkipsDisabledTargets"
    (view.resolve [name, [.field "age"]] == some (.edit [.field "age"]))
  let repeated : List Diagnostic := [
    { kind := .error, message := "First", targets := .locations name [name] },
    { kind := .error, message := "Second", targets := .locations name [] },
    { kind := .error, message := "First", targets := .locations name [] }]
  let controls := (fields.evaluate Person.initial Env.nil (diagnostics := repeated)).view.controls
  check "InlineMessagesAreDistinctAndOrdered"
    ((controls.find? (·.location == name)).map (·.errors) == some ["First", "Second"])

  let _ : Validation Person := {
    validate := fun _ => .error [{
      message := "Check the form and name"
      targets := .locations .self [.field Person.Field.name .self] }] }
  let resolution : Component [] Person.Raw := .observe .issues <|
    .group "Resolution" [
      .field path[Person.Field.age] "Age" .natural,
      .field path[Person.Field.name] "Name" .text,
      .button "Visit" (.visit {
        inputs := inputs[.ui (Ref.here : InputRef _ (List Issue))]
        run := fun issues => issues.head?.bind (·.destination?) })]
  let initial := ModelForm.openState (model := Person) (supply := supply) resolution Person.initial Env.nil
  let submitted := ModelForm.submit initial
  let some visit := initial.evaluation.view.controls.find? (·.label == "Visit")
    | throw (IO.userError "Missing visit control")
  let visited ← IO.ofExcept (ModelForm.execute (model := Person) resolution initial
    (.apply visit.key none))
  check "SubmitAndVisitPreferExactTargetsOverEarlierDescendants"
    (focuses submitted == [.edit name] && focuses visited == focuses submitted)

  let _ : Validation Person := {
    validate := fun _ => .error [
      { message := "Check the age"
        targets := .locations (.field Person.Field.age .self) },
      { message := "Check the address"
        targets := .locations (.field Person.Field.address .self) }] }
  let ordered : Component [] Person.Raw := .group "Ordered" [
    .field path[Person.Field.address, Address.Field.street] "Street" .text,
    .field path[Person.Field.age] "Age" .natural]
  let submitted := ModelForm.submit
    (ModelForm.openState (model := Person) (supply := supply) ordered Person.initial Env.nil)
  check "SubmitFocusesTheFirstRenderedIssue" (focuses submitted == [.edit street])

end Tests.Navigation
