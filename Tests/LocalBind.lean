module

public import Forms.ExampleForms.Registry

public section
namespace Tests.LocalBind
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private def control
  {α : Type}
  {form : Component [] α}
  (state : ModelForm.State form)
  (label : String)
  (nth : Nat := 0)
  : IO ControlKey := do
  let controls := (ModelView.render form state.value state.cache [] Env.nil state.locals).controls
  let some found := (controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"FAIL missing local control {label} {nth}")
  return found.key

private def apply {model : Type} [FormModel model] [Validation model]
    (form : Component [] (FormModel.Raw model)) (state : ModelForm.State form)
    (label : String) (argument : Option Input := none) (nth : Nat := 0) : IO (ModelForm.State form) := do
  IO.ofExcept (ModelForm.execute (model := model) form state
    (.apply (← control state label nth) argument))

@[expose] def row : Component [] (List Nat) := .bind RowSelection.none
  (.table .self "Choices" "Choice" 0
    columns["Number" => .computed "Number" { inputs := inputs[path[]], run := toString }]
    (some .here))

@[expose] def rows : Component [] (List (List Nat)) :=
  .list .self "Rows" "Row" [0] row

private def rowSelection (state : ModelForm.State rows) (index : Nat) : RowSelection :=
  let locals : List row.LocalState := state.locals
  ((locals[index]?).getD row.initialState).value

private def loadedBody : Status Bool → Component [] ExpenseReport.Raw
  | .ready true => .bind RowSelection.none (.table path[ExpenseReport.Field.expenses]
      "Expenses" "Expense" ⟨"", 0, false⟩ columns[] (some .here))
  | .ready false => .bind (fun n : Nat => n + 1) (.computed "Function" {
      inputs := inputs[.ui (Ref.here : Var [⟨.writable, Nat → Nat⟩] (Nat → Nat))]
      run := fun f => toString (f 41) })
  | _ => .computed "Status" (.const "Loading")

private def mode : Component [] ExpenseReport.Raw := .group "Local load" [
  .field path[ExpenseReport.Field.employee] "Mode" .text,
  .load { inputs := inputs[path[ExpenseReport.Field.employee]], run := fun name => Source.pure (name == "table") }
    loadedBody]

def run : IO Unit := do
  let opened := ModelForm.openState rows [[10, 20], [30, 40]] Env.nil
  let selected ← apply (model := List (List Nat)) rows opened "Select" none 3
  check "LocalListRowsHaveIndependentBindings"
    (rowSelection selected 0 == .none && rowSelection selected 1 == .row 1 && selected.value == opened.value)
  let remove := DisplayProtocol.controlKey .remove [.index 0]
  let removed ← IO.ofExcept (ModelForm.execute (model := List (List Nat)) rows selected (.apply remove none))
  check "LocalListBindingFollowsRowRemoval"
    (removed.value == [[30, 40]] && rowSelection removed 0 == .row 1)
  let added ← apply (model := List (List Nat)) rows removed "Add row"
  check "LocalListNewRowStartsFresh"
    (rowSelection added 0 == .row 1 && rowSelection added 1 == .none)
  let reset ← IO.ofExcept (ModelForm.execute (model := List (List Nat)) rows added .reset)
  check "LocalListResetRestoresInitialBindings"
    (reset.value == opened.value && rowSelection reset 0 == .none && rowSelection reset 1 == .none)
  let nested : Component [] (List Nat) := .bind RowSelection.none (.bind RowSelection.none
    (.table .self "Nested" "Number" 0 columns[] (some (.there .here))))
  let nestedOpened := ModelForm.openState nested [10, 20] Env.nil
  let nestedSelected ← apply (model := List Nat) nested nestedOpened "Select"
  check "LocalNestedBindingCanReferenceOuterVariable"
    (nestedSelected.locals.value == .row 0 && nestedSelected.locals.tail.value == .none)
  let initial := { ExpenseReport.initial with employee := "table" }
  let loaded := ModelForm.load mode (ModelForm.openState mode initial Env.nil)
  let picked ← apply (model := ExpenseReport) mode loaded "Select" none 1
  let same ← apply (model := ExpenseReport) mode picked "Mode" (some (.text "table"))
  check "LocalLoadRetainsStateForSameStatus"
    ((ModelView.render mode same.value same.cache [] Env.nil same.locals).controls.any (·.label == "Selected"))
  let changed ← apply (model := ExpenseReport) mode same "Mode" (some (.text "function"))
  check "LocalLoadCanChangeBindingTypes" (match (ModelView.render mode changed.value changed.cache [] Env.nil changed.locals).view with
    | .stack _ [_, .computed "Function" "42"] => true
    | _ => false)
  let back ← apply (model := ExpenseReport) mode changed "Mode" (some (.text "table"))
  check "LocalLoadResetsBindingsWhenStatusChanges"
    (!(ModelView.render mode back.value back.cache [] Env.nil back.locals).controls.any (·.label == "Selected") &&
      toJson back.value.expenses == toJson initial.expenses)

end Tests.LocalBind
