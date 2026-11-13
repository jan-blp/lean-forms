module

public import Forms.ExampleForms.Registry

public section
namespace Tests.TableSelection
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private abbrev form := ExpenseReport.focusForm
private abbrev BrowserState := ModelForm.State form
private def selection (state : BrowserState) : RowSelection := state.locals.value

private def browse (state : BrowserState) (input : ModelForm.Event) : IO BrowserState :=
  IO.ofExcept (ModelForm.execute (model := ExpenseReport) form state input)

private def browserKey
  (state : BrowserState)
  (label : String)
  (nth : Nat := 0)
  : IO ControlKey := do
  let controls := (ModelView.render form state.value state.cache [] state.env state.locals).controls
  let some control := (controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"FAIL no selection control {label} {nth}")
  return control.key

def run : IO Unit := do
  let opened := ModelForm.openState form ExpenseReport.initial Env.nil
  let first ← browserKey opened "Select"
  let second ← browserKey opened "Select" 1
  let selected ← browse opened (.apply second none)
  check "TableSelectKeepsItems"
    (selection selected == .row 1 &&
      toJson selected.value == toJson opened.value &&
      selection opened == .none)
  check "TableSelectedRowMarked" (match (ModelView.render form selected.value {} [] selected.env selected.locals).view with
    | .stack _ (_ :: .table _ _ rows _ _ :: _) => rows.map (·.selected) == [some false, some true]
    | _ => false)
  let description ← browserKey selected "Description"
  let edited ← browse selected (.apply description (some (.text "Updated hotel")))
  check "TableDetailsEditSelectedItem"
    (edited.value.expenses.map (·.description) == ["Train to Bern", "Updated hotel"])
  let switched ← browse edited (.apply first none)
  let stale ← browse switched (.apply description (some (.text "Stale")))
  check "TableOldDetailsRejectStaleEdit"
    (stale.ui.rejection == some (toString InvocationError.absent) &&
      toJson stale.value == toJson switched.value)
  let selectedAgain ← browse edited (.apply second none)
  let removedEarlier ← browse selectedAgain (.apply (← browserKey selectedAgain "Remove") none)
  check "TableRemoveEarlierKeepsSelectedItem"
    (selection removedEarlier == .row 0 &&
      removedEarlier.value.expenses.map (·.description) == ["Updated hotel"])
  let remainingDetail ← browserKey removedEarlier "Description"
  let removedSelected ← browse removedEarlier (.apply (← browserKey removedEarlier "Remove") none)
  check "TableRemoveSelectedClearsSelection"
    (selection removedSelected == .none && removedSelected.value.expenses.isEmpty)
  let staleAfterRemove ← browse removedSelected (.apply remainingDetail (some (.text "Stale")))
  check "TableRemovedDetailsRejectStaleEdit"
    (staleAfterRemove.ui.rejection == some (toString InvocationError.absent))
  let reset ← browse edited .reset
  check "TableResetClearsSelection"
    (selection reset == .none && toJson reset.value == toJson ExpenseReport.initial)
  let disabled := Component.disabledWhen (.const true) form
  let rejected ← IO.ofExcept (ModelForm.execute (model := ExpenseReport) disabled (ModelForm.openState disabled ExpenseReport.initial Env.nil)
    (.apply second none))
  check "TableDisabledSelectionRejects"
    (rejected.ui.rejection == some (toString InvocationError.disabled) &&
      toJson rejected.value == toJson opened.value)
  let pending := { opened with ui := { opened.ui with pending := true } }
  let rejectedPending ← browse pending (.apply second none)
  check "TablePendingSelectionRejects"
    (rejectedPending.ui.rejection == some "Submission is in progress." &&
      toJson rejectedPending.value == toJson opened.value)
  let request : HttpRequest := { method := .post, url := "/api/details", body := none }
  let loading : Component [] ExpenseReport.Raw := .bind RowSelection.none (.focus
    (target := {
      inputs := inputs[.ui (Ref.here : Var [⟨.writable, RowSelection⟩] RowSelection)]
      run := RowSelection.itemPath path[ExpenseReport.Field.expenses]
    })
    (body := .loadWith (.const (.fetch request (fromJson? (α := String))))
      (fun details => .computed "Details" (.const details))))
  let selectedLocals : loading.LocalState := { loading.initialState with value := .row 1 }
  check "FocusLoadsOnlySelectedDetails"
    ((loading.requests {} opened.value Env.nil).isEmpty &&
      loading.requests {} selected.value Env.nil selectedLocals == [request])
  let table : Component [] ExpenseReport.Raw := .bind RowSelection.none (.table
    path[ExpenseReport.Field.expenses] "Expenses" "Expense" ⟨"", 0, false⟩ columns[] (some .here))
  let twoTables := Component.group "Two selections" [table, table]
  let multiple := ModelForm.openState twoTables ExpenseReport.initial Env.nil
  let selectors := (ModelView.render twoTables multiple.value {} [] Env.nil multiple.locals).controls.filter (·.label == "Select")
  check "LocalBindingsKeepViewsIndependent" (selectors.length == 4)
  let some secondTableRow := selectors[3]? | throw (IO.userError "FAIL missing second table selection")
  let independent ← IO.ofExcept (ModelForm.execute (model := ExpenseReport) twoTables multiple
    (.apply secondTableRow.key none))
  check "SelectionChangesOnlyItsBinding"
    (independent.locals.value.value == .none && independent.locals.tail.value.value == .row 1 &&
      toJson independent.value == toJson multiple.value)
  let nested : Component [] ExpenseReport.Raw := .focus
    (.const (.ofPath path[ExpenseReport.Field.expenses]))
    (.bind RowSelection.none (.table .self "Nested" "Expense" ⟨"", 0, false⟩ columns[] (some .here)))
  let nestedOpened := ModelForm.openState nested ExpenseReport.initial Env.nil
  let some nestedSelect := (ModelView.render nested nestedOpened.value {} [] Env.nil).controls.find? (·.label == "Select")
    | throw (IO.userError "FAIL missing nested selection")
  let nestedSelected ← IO.ofExcept (ModelForm.execute (model := ExpenseReport) nested nestedOpened
    (.apply nestedSelect.key none))
  check "FocusPreservesNestedUiUpdates"
    (nestedSelected.locals.value == .row 0 && toJson nestedSelected.value == toJson nestedOpened.value)
  let mixed : Component [⟨.readOnly, RowSelection⟩, ⟨.writable, RowSelection⟩] ExpenseReport.Raw :=
    .bind false (.table path[ExpenseReport.Field.expenses] "Expenses" "Expense" ⟨"", 0, false⟩
      columns[] (some (.there (.there .here))))
  let mixedOpened := ModelForm.openState mixed ExpenseReport.initial env[.row 1, .none]
  let some mixedSelect := (ModelView.render mixed mixedOpened.value {} [] mixedOpened.env).controls.find?
      (·.label == "Select")
    | throw (IO.userError "FAIL missing selection in mixed context")
  let mixedSelected ← IO.ofExcept (ModelForm.execute (model := ExpenseReport) mixed mixedOpened
    (.apply mixedSelect.key none))
  check "TableSelectionPreservesReadOnlyInputs"
    (mixedSelected.env.value == .row 1 && mixedSelected.env.tail.value == .row 0 &&
      mixedSelected.locals.value == false &&
      toJson mixedSelected.value == toJson mixedOpened.value)

end Tests.TableSelection
