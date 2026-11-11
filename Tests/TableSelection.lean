module

public import Forms.ExampleForms.Registry

public section
namespace Tests.TableSelection
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private abbrev BrowserState := ModelForm.State ExpenseReport.Raw

private def browse (state : BrowserState) (command : ModelForm.Command) : IO BrowserState :=
  IO.ofExcept (ModelForm.execute (model := ExpenseReport) ExpenseReport.focusForm state command)

private def browserKey
  (state : BrowserState)
  (label : String)
  (nth : Nat := 0)
  : IO ControlKey := do
  let controls := (ModelView.render ExpenseReport.focusForm state.value state.cache [] state.ui.components).controls
  let some control := (controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"FAIL no selection control {label} {nth}")
  return control.key

def run : IO Unit := do
  let opened := ModelForm.openState ExpenseReport.initial
  let first ← browserKey opened "Select"
  let second ← browserKey opened "Select" 1
  let selected ← browse opened (.event (.apply second none))
  check "TableSelectKeepsItems"
    (ExpenseReport.selection.get selected.ui.components == .row 1 &&
      toJson selected.value == toJson opened.value &&
      ExpenseReport.selection.get opened.ui.components == .none)
  check "TableSelectedRowMarked" (match (ModelView.render ExpenseReport.focusForm selected.value {} [] selected.ui.components).view with
    | .stack _ (_ :: .table _ _ rows _ _ :: _) => rows.map (·.selected) == [some false, some true]
    | _ => false)
  let description ← browserKey selected "Description"
  let edited ← browse selected (.event (.apply description (some (.text "Updated hotel"))))
  check "TableDetailsEditSelectedItem"
    (edited.value.expenses.map (·.description) == ["Train to Bern", "Updated hotel"])
  let switched ← browse edited (.event (.apply first none))
  let stale ← browse switched (.event (.apply description (some (.text "Stale"))))
  check "TableOldDetailsRejectStaleEdit"
    (stale.ui.rejection == some (toString InvocationError.absent) &&
      toJson stale.value == toJson switched.value)
  let selectedAgain ← browse edited (.event (.apply second none))
  let removedEarlier ← browse selectedAgain (.event (.apply (← browserKey selectedAgain "Remove") none))
  check "TableRemoveEarlierKeepsSelectedItem"
    (ExpenseReport.selection.get removedEarlier.ui.components == .row 0 &&
      removedEarlier.value.expenses.map (·.description) == ["Updated hotel"])
  let remainingDetail ← browserKey removedEarlier "Description"
  let removedSelected ← browse removedEarlier (.event (.apply (← browserKey removedEarlier "Remove") none))
  check "TableRemoveSelectedClearsSelection"
    (ExpenseReport.selection.get removedSelected.ui.components == .none && removedSelected.value.expenses.isEmpty)
  let staleAfterRemove ← browse removedSelected (.event (.apply remainingDetail (some (.text "Stale"))))
  check "TableRemovedDetailsRejectStaleEdit"
    (staleAfterRemove.ui.rejection == some (toString InvocationError.absent))
  let reset ← browse edited (.event .reset)
  check "TableResetClearsSelection"
    (ExpenseReport.selection.get reset.ui.components == .none && toJson reset.value == toJson ExpenseReport.initial)
  let disabled := Component.disabledWhen (.const true) ExpenseReport.focusForm
  let rejected ← IO.ofExcept (ModelForm.execute (model := ExpenseReport) disabled opened
    (.event (.apply second none)))
  check "TableDisabledSelectionRejects"
    (rejected.ui.rejection == some (toString InvocationError.disabled) &&
      toJson rejected.value == toJson opened.value)
  let pending := { opened with ui := { opened.ui with pending := true } }
  let rejectedPending ← browse pending (.event (.apply second none))
  check "TablePendingSelectionRejects"
    (rejectedPending.ui.rejection == some "Submission is in progress." &&
      toJson rejectedPending.value == toJson opened.value)
  let request : HttpRequest := { method := .post, url := "/api/details", body := none }
  let loading : Component ExpenseReport.Raw := .focus
    (target := {
      inputs := inputs[.ui ExpenseReport.selection]
      run := RowSelection.itemPath path[ExpenseReport.Field.expenses]
    })
    (body := .bind (.const (.fetch request (fromJson? (α := String))))
      (fun details => .computed "Details" (.const details)))
  check "FocusLoadsOnlySelectedDetails"
    ((loading.requests {} opened.value opened.ui.components).isEmpty && loading.requests {} selected.value selected.ui.components == [request])
  -- Two views of the same data may keep independent UI selections.
  let other : UiStateKey RowSelection := ⟨"other-expense", .none⟩
  let table (selection : UiStateKey RowSelection) : Component ExpenseReport.Raw := .table
    path[ExpenseReport.Field.expenses] "Expenses" "Expense" ⟨"", 0, false⟩
    columns[] (some selection)
  let twoTables := Component.group "Two selections" [table ExpenseReport.selection, table other]
  let selectors := (ModelView.render twoTables opened.value {}).controls.filter (·.label == "Select")
  check "SelectionKeysKeepViewsIndependent" (selectors.length == 4)
  let some secondTableRow := selectors[3]? | throw (IO.userError "FAIL missing second table selection")
  let independent ← IO.ofExcept (ModelForm.execute (model := ExpenseReport) twoTables opened
    (.event (.apply secondTableRow.key none)))
  check "SelectionChangesOnlyItsUiEntry"
    (other.get independent.ui.components == .row 1 &&
      ExpenseReport.selection.get independent.ui.components == .none &&
      toJson independent.value == toJson opened.value)
  let nested : Component ExpenseReport.Raw := .focus
    (.const (.ofPath path[ExpenseReport.Field.expenses]))
    (.table .self "Nested" "Expense" ⟨"", 0, false⟩ columns[] (some other))
  let some nestedSelect := (ModelView.render nested opened.value {}).controls.find? (·.label == "Select")
    | throw (IO.userError "FAIL missing nested selection")
  let nestedSelected ← IO.ofExcept (ModelForm.execute (model := ExpenseReport) nested opened
    (.event (.apply nestedSelect.key none)))
  check "FocusPreservesNestedUiUpdates"
    (other.get nestedSelected.ui.components == .row 0 &&
      toJson nestedSelected.value == toJson opened.value)

end Tests.TableSelection
