module

public import Forms.ExampleForms.SharedState
public import Forms.Runtime.ModelForm

public section
namespace Tests.SharedState
open Forms.Model Forms.Runtime
open Forms.ExampleForms.SharedState

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private def key
  {α : Type}
  {component : Component [] α}
  (state : ModelForm.State component)
  (label : String)
  (nth : Nat := 0)
  : IO ControlKey := do
  let controls := (ModelView.render component state.value state.cache [] state.env state.locals).controls
  let some control := (controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"FAIL missing {label} {nth}")
  return control.key

private def press
  (state : ModelForm.State form)
  (label : String)
  (nth : Nat := 0)
  : IO (ModelForm.State form) := do
  IO.ofExcept (ModelForm.execute (model := List Nat) form state (.apply (← key state label nth) none))

mutual
private def outputs (label : String) : Display.View → List String
  | .computed name value => if name == label then [value] else []
  | .stack _ children => outputsAll label children
  | .list (children := children) .. => outputsAll label children
  | .table (rows := rows) (footer := footer) .. => outputsRows label rows ++ outputs label footer
  | _ => []

private def outputsAll (label : String) : List Display.View → List String
  | [] => []
  | view :: rest => outputs label view ++ outputsAll label rest

private def outputsRows (label : String) : List Display.TableRow → List String
  | [] => []
  | { cells, .. } :: rest => outputsAll label cells ++ outputsRows label rest
end

private def values (state : ModelForm.State form) (label : String) : List String :=
  outputs label (ModelView.render form state.value state.cache [] state.env state.locals).view

def run : IO Unit := do
  let opened := ModelForm.openState form initial Env.nil
  let first ← press opened "Increment shared"
  check "SharedStateUpdatesEveryConsumer"
    (values first "Shared count" == ["1", "1"] &&
      values first "Shared count outside the list" == ["1"] && first.value == initial)
  let second ← press first "Increment shared" 1
  check "SharedStateUpdatesReadLatestValue" (values second "Shared count" == ["2", "2"])
  let privateFirst ← press second "Increment private"
  let privateSecond ← press privateFirst "Increment private" 1
  let privateAgain ← press privateSecond "Increment private" 1
  check "SharedConsumersRetainIndependentPrivateState"
    (values privateAgain "Private count" == ["1", "2"] && values privateAgain "Shared count" == ["2", "2"])
  let removed ← press privateAgain "Remove"
  check "RemovingConsumerPreservesOwnerAndOtherConsumer"
    (removed.value == [20] && values removed "Shared count" == ["2"] && values removed "Private count" == ["2"])
  let empty ← press removed "Remove"
  check "SharedOwnerOutlivesAllConsumers"
    (empty.value.isEmpty && values empty "Shared count outside the list" == ["2"])
  let added ← press empty "Add consumer"
  check "NewConsumerReadsSharedStateAndStartsPrivateState"
    (values added "Shared count" == ["2"] && values added "Private count" == ["0"])
  let cleared ← press added "Clear shared"
  check "SiblingCanUpdateSharedState" (values cleared "Shared count" == ["0"])
  let reset ← IO.ofExcept (ModelForm.execute (model := List Nat) form privateAgain .reset)
  check "ResetRestoresSharedAndPrivateState"
    (reset.value == initial && values reset "Shared count" == ["0", "0"] &&
      values reset "Private count" == ["0", "0"])

  let independent := Component.group "Independent owners" [form, form]
  let independentOpened := ModelForm.openState independent initial Env.nil
  let independentChanged ← IO.ofExcept (ModelForm.execute (model := List Nat) independent independentOpened
    (.apply (← key independentOpened "Increment shared" 2) none))
  check "RepeatedOwnersKeepSeparateSharedState"
    (outputs "Shared count outside the list"
      (ModelView.render independent independentChanged.value {} [] Env.nil independentChanged.locals).view == ["0", "1"])

  -- Both tables use the same binding; removal also adjusts that binding.
  let tables : Component [] (List Nat) := .bind RowSelection.none <|
    .group "Two views" [
      Component.void <| .table .self "First" "Item" 0 columns[] (some .here),
      Component.void <| .table .self "Second" "Item" 0 columns[] (some .here),
      .computed "Selection" {
        inputs := inputs[.ui (Ref.here : Var _ RowSelection)]
        run := fun selection => match selection with
          | .none => "None"
          | .row index => toString index }]
  let tablesOpened := ModelForm.openState tables [10, 20] Env.nil
  let selected ← IO.ofExcept (ModelForm.execute (model := List Nat) tables tablesOpened
    (.apply (← key tablesOpened "Select" 1) none))
  check "ExistingTablesShareSelectionBinding" (match
      (ModelView.render tables selected.value {} [] Env.nil selected.locals).view with
    | .stack (children := [.table (rows := first) .., .table (rows := second) .., _]) .. =>
      first.map (·.selected) == [some false, some true] &&
      second.map (·.selected) == [some false, some true]
    | _ => false)
  let removedFromTable ← IO.ofExcept (ModelForm.execute (model := List Nat) tables selected
    (.apply (← key selected "Remove") none))
  check "ExistingTableOperationUpdatesModelAndSharedState"
    (removedFromTable.value == [20] && removedFromTable.locals.value == .row 0 &&
      outputs "Selection" (ModelView.render tables removedFromTable.value {} [] Env.nil removedFromTable.locals).view == ["0"])

end Tests.SharedState
