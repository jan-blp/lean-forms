module

public import Forms.ExampleForms.Registry

public section
namespace Tests.TableSelection
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private abbrev BrowserState := ModelForm.State ExpenseBrowser.Raw

private def browse (state : BrowserState) (command : ModelForm.Command) : IO BrowserState :=
  IO.ofExcept (ModelForm.execute (model := ExpenseBrowser) ExpenseBrowser.form state command)

private def browserKey (state : BrowserState) (label : String) (nth : Nat := 0) : IO ControlKey := do
  let controls := (ModelView.render ExpenseBrowser.form state.value state.cache).controls
  let some control := (controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"FAIL no selection control {label} {nth}")
  return control.key

def run : IO Unit := do
  let opened := ModelForm.openState ExpenseBrowser.initial
  let first ← browserKey opened "Select"
  let second ← browserKey opened "Select" 1
  let selected ← browse opened (.event (.apply second none))
  check "TableSelectKeepsItems"
    (selected.value.selection == .row 1 &&
      toJson selected.value.report.expenses == toJson opened.value.report.expenses)
  check "TableSelectedRowMarked" (match (ModelView.render ExpenseBrowser.form selected.value {}).view with
    | .stack _ (_ :: .table _ _ rows _ _ :: _) => rows.map (·.selected) == [some false, some true]
    | _ => false)
  let description ← browserKey selected "Description"
  let edited ← browse selected (.event (.apply description (some (.text "Updated hotel"))))
  check "TableDetailsEditSelectedItem"
    (edited.value.report.expenses.map (·.description) == ["Train to Bern", "Updated hotel"])
  let switched ← browse edited (.event (.apply first none))
  let stale ← browse switched (.event (.apply description (some (.text "Stale"))))
  check "TableOldDetailsRejectStaleEdit"
    (stale.ui.rejection == some (toString InvocationError.absent) &&
      toJson stale.value == toJson switched.value)
  let selectedAgain ← browse edited (.event (.apply second none))
  let removedEarlier ← browse selectedAgain (.event (.apply (← browserKey selectedAgain "Remove") none))
  check "TableRemoveEarlierKeepsSelectedItem"
    (removedEarlier.value.selection == .row 0 &&
      removedEarlier.value.report.expenses.map (·.description) == ["Updated hotel"])
  let remainingDetail ← browserKey removedEarlier "Description"
  let removedSelected ← browse removedEarlier (.event (.apply (← browserKey removedEarlier "Remove") none))
  check "TableRemoveSelectedClearsSelection"
    (removedSelected.value.selection == .none && removedSelected.value.report.expenses.isEmpty)
  let staleAfterRemove ← browse removedSelected (.event (.apply remainingDetail (some (.text "Stale"))))
  check "TableRemovedDetailsRejectStaleEdit"
    (staleAfterRemove.ui.rejection == some (toString InvocationError.absent))
  let reset ← browse edited (.event .reset)
  check "TableResetClearsSelection"
    (reset.value.selection == .none && toJson reset.value == toJson ExpenseBrowser.initial)
  let disabled := Component.disabledWhen (.const true) ExpenseBrowser.form
  let rejected ← IO.ofExcept (ModelForm.execute (model := ExpenseBrowser) disabled opened
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
  let loading : Component ExpenseBrowser.Raw := .focus
    (target := {
      inputs := inputs[path[ExpenseBrowser.Field.selection]]
      run := RowSelection.itemPath path[ExpenseBrowser.Field.report, ExpenseReport.Field.expenses]
    })
    (body := .bind (.const (.fetch request (fromJson? (α := String))))
      (fun details => .computed "Details" (.const details)))
  check "FocusLoadsOnlySelectedDetails"
    ((loading.requests {} opened.value).isEmpty && loading.requests {} selected.value == [request])

end Tests.TableSelection
