module

public import Forms.ExampleForms.Registry
public import Tests.FreshId

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

private def apply
  {model : Type}
  [FormModel model]
  [Validation model]
  (form : Component [] (Raw model))
  (state : ModelForm.State form)
  (label : String)
  (argument : Option Input := none)
  (nth : Nat := 0)
  : IO (ModelForm.State form) := do
  IO.ofExcept (ModelForm.execute (model := model) form state
    (.apply (← control state label nth) argument))

@[expose] def row : Component [] (List (Item Nat)) := .bind RowSelection.none
  (Component.void <| .table .self "Choices" (.numbered "Choice") "Add choice"
    (Item.mkWithoutUuid 0)
    columns["Number" => .computed "Number" { inputs := inputs[path[Item.Field.value]], run := toString }]
    (some .here))

@[expose] def rows : Component [] (List (Item (List (Item Nat)))) :=
  Component.void <| .list .self "Rows" (.numbered "Row") "Add row" (Item.mkWithoutUuid [])
    (.zoom path[Item.Field.value] row)

private def rowSelection (state : ModelForm.State rows) (index : Nat) : RowSelection :=
  let local? := state.value[index]?.bind (state.locals.producer.producer[·.id]?)
  ((local?.map (·.producer)).getD row.initialState).value

private def loadedBody : Status Bool → Component [] ExpenseReport.Raw
  | .ready true => .bind RowSelection.none (Component.void <| .table path[ExpenseReport.Field.expenses]
      "Expenses" (.numbered "Expense") "Add expense" Expense.initial columns[]
      (some .here))
  | .ready false => .bind (fun n : Nat => n + 1) (.computed "Function" {
      inputs := inputs[.ui (Ref.here : Var [⟨.writable, Nat → Nat⟩] (Nat → Nat))]
      run := fun f => toString (f 41) })
  | _ => .computed "Status" (.const "Loading")

private def mode : Component [] ExpenseReport.Raw := .group "Local load" [
  .field path[ExpenseReport.Field.employee] "Mode" .text,
  .load { inputs := inputs[path[ExpenseReport.Field.employee]], run := fun name => Source.pure (name == "table") }
    loadedBody]

def run : IO Unit := do
  let value : List (Item (List (Item Nat))) := [
    ⟨firstId, [⟨firstId, 10⟩, ⟨secondId, 20⟩]⟩,
    ⟨secondId, [⟨firstId, 30⟩, ⟨secondId, 40⟩]⟩]
  let opened := ModelForm.openState (model := List (Item (List (Item Nat)))) (supply := supply) rows
    value Env.nil
  let selected ← apply (model := List (Item (List (Item Nat)))) rows opened "Select" none 3
  check "LocalListRowsHaveIndependentBindings"
    (rowSelection selected 0 == .none && rowSelection selected 1 == .row secondId &&
      selected.value == opened.value)
  let removed ← apply (model := List (Item (List (Item Nat)))) rows selected "Remove" none 2
  check "LocalListBindingFollowsRowRemoval"
    (removed.value.map (·.value.map (·.value)) == [[30, 40]] && rowSelection removed 0 == .row secondId)
  let added ← apply (model := List (Item (List (Item Nat)))) rows removed "Add row"
  check "LocalListNewRowStartsFresh"
    (rowSelection added 0 == .row secondId && rowSelection added 1 == .none)
  let reset ← IO.ofExcept (ModelForm.execute (model := List (Item (List (Item Nat)))) rows added .reset)
  check "LocalListResetRestoresInitialBindings"
    (reset.value == opened.value && rowSelection reset 0 == .none && rowSelection reset 1 == .none)
  let nested : Component [] (List (Item Nat)) := .bind RowSelection.none (.bind RowSelection.none
    (Component.void <| .table .self "Nested" (.numbered "Number") "Add number"
        (Item.mkWithoutUuid 0) columns[] (some (.there .here))))
  let nestedOpened := ModelForm.openState (model := List (Item Nat)) (supply := supply) nested
    [⟨firstId, 10⟩, ⟨secondId, 20⟩] Env.nil
  let nestedSelected ← apply (model := List (Item Nat)) nested nestedOpened "Select"
  check "LocalNestedBindingCanReferenceOuterVariable"
    (nestedSelected.locals.value == .row firstId && nestedSelected.locals.tail.producer.value == .none)
  let initial := { ExpenseReport.initial with employee := "table" }
  let loaded := ModelForm.load mode
    (ModelForm.openState (model := ExpenseReport) (supply := supply) mode initial Env.nil)
  let picked ← apply (model := ExpenseReport) mode loaded "Select" none 1
  let same ← apply (model := ExpenseReport) mode picked "Mode" (some (.text "table"))
  check "LocalLoadRetainsStateForSameStatus"
    ((ModelView.render mode same.value same.cache [] Env.nil same.locals).controls.any (·.label == "Selected"))
  let changed ← apply (model := ExpenseReport) mode same "Mode" (some (.text "function"))
  check "LocalLoadCanChangeBindingTypes" (match (ModelView.render mode changed.value changed.cache [] Env.nil changed.locals).view with
    | .stack (children := [_, .computed "Function" "42"]) .. => true
    | _ => false)
  let back ← apply (model := ExpenseReport) mode changed "Mode" (some (.text "table"))
  check "LocalLoadResetsBindingsWhenStatusChanges"
    (!(ModelView.render mode back.value back.cache [] Env.nil back.locals).controls.any (·.label == "Selected") &&
      toJson back.value.expenses == toJson initial.expenses)

end Tests.LocalBind
