module

public import Forms.ExampleForms.Registry

public section
namespace Tests.Table
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private abbrev State := ModelForm.State ExpenseReport.Raw

private def execute (state : State) (command : ModelForm.Command) : IO State :=
  IO.ofExcept (ModelForm.execute (model := ExpenseReport) ExpenseReport.form state command)

private def rendered (state : State) : ModelView.Rendered :=
  ModelView.render ExpenseReport.form state.value state.cache

private def key (state : State) (label : String) (nth : Nat := 0) : IO ControlKey := do
  let some control := ((rendered state).controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"FAIL no table control {label} {nth}")
  return control.key

private def apply (state : State) (label : String) (argument : Option Input) (nth : Nat := 0)
    : IO State := do
  execute state (.event (.apply (← key state label nth) argument))

def run : IO Unit := do
  let opened := ModelForm.openState ExpenseReport.initial
  check "TableHeadersAndRows" (match (rendered opened).view with
    | .stack _ [_, .table "Expenses" headers rows _ _, _] =>
      headers == ["Description", "Amount (CHF)", "Receipt", "Actions"] &&
      rows.map (·.cells.length) == [4, 4] && rows.map (·.label) == ["Expense 1", "Expense 2"]
    | _ => false)
  let wire := (ModelForm.snapshot (model := ExpenseReport) ExpenseReport.form opened).view.toReact false
  check "TableHiddenCellKeepsColumn" (match wire with
    | some (.group { children := [_, .table table, _], .. }) =>
      match table.rows with
      | first :: second :: _ =>
        first.cells[2]? == some (.group { label := none, children := [], error := none }) &&
        (match first.cells[3]? with | some (FormsReact.Component.button _) => true | _ => false) &&
        (match second.cells[2]? with | some (FormsReact.Component.checkbox _) => true | _ => false)
      | _ => false
    | _ => false)
  let edited ← apply opened "Description" (some (.text "Taxi")) 1
  check "TableEditsOnlyTargetRow"
    (edited.value.expenses.map (·.description) == ["Train to Bern", "Taxi"])
  let invalid ← apply edited "Amount (CHF)" (some (.text "-1"))
  check "TableRejectsInvalidInput"
    (invalid.ui.rejection == some "Enter a non-negative whole number." &&
      toJson invalid.value == toJson edited.value)
  let visible ← apply edited "Amount (CHF)" (some (.text "100"))
  check "TableCellVisibility" (((rendered visible).controls.filter (·.label == "Receipt attached")).length == 2)
  let disabled := Component.disabledWhen (.const true) ExpenseReport.form
  let disabledState ← IO.ofExcept (ModelForm.execute (model := ExpenseReport) disabled opened
    (.event (.apply (← key opened "Remove") none)))
  check "TableDisabledRemoveRejects"
    (disabledState.ui.rejection == some (toString InvocationError.disabled) &&
      toJson disabledState.value == toJson opened.value)
  let last ← key opened "Description" 1
  let removed ← apply edited "Remove" none 1
  check "TableRemovesOnlyTargetRow"
    (removed.value.expenses.map (·.description) == ["Train to Bern"])
  let stale ← execute removed (.event (.apply last (some (.text "Stale"))))
  check "TableRemovedRowRejectsStaleEdit"
    (stale.ui.rejection == some (toString InvocationError.absent) &&
      toJson stale.value == toJson removed.value)
  let empty ← apply removed "Remove" none
  check "TableEmptyKeepsHeaders" (match (rendered empty).view with
    | .stack _ [_, .table _ headers [] _ _, _] => headers.length == 4
    | _ => false)
  let added ← apply empty "Add expense" none
  check "TableAddsInitialRow"
    (toJson added.value.expenses == toJson ([⟨"", 0, false⟩] : List Expense.Raw))
  let validated ← execute added (.event .submit)
  check "TableValidatesCells"
    ((ModelForm.snapshot (model := ExpenseReport) ExpenseReport.form validated).errors.map (·.message) ==
      ["Describe the expense.", "Enter an amount of at least CHF 1."])
  let request (amount : Nat) : HttpRequest := { method := .post, url := s!"/api/expense/{amount}", body := none }
  let loading : Component ExpenseReport.Raw := .table
    path[ExpenseReport.Field.expenses] "Expenses" "Expense" ⟨"", 0, false⟩
    columns["Details" => .bind
      { inputs := inputs[path[Expense.Field.amount]], run := fun amount =>
          Source.fetch (request amount) (fromJson? (α := String)) }
      (fun details => .computed "Details" (.const details))]
  check "TableRequestsEveryRow" (loading.requests {} opened.value == [request 58, request 180])

end Tests.Table
