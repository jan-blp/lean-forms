module

public import Forms.ExampleForms.Outputs
public import Forms.Runtime.ModelForm

public section
namespace Tests.OutputEvaluation
open Forms.Model
open Forms.Runtime Forms.Runtime.ModelView
open Forms.ExampleForms.Outputs

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

private def press
  {α state β : Type}
  (evaluated : Evaluated [] α state β)
  (label : String)
  (nth : Nat := 0)
  (argument : Option Input := none)
  : IO (ComponentUpdate [] α state) := do
  let some control := (evaluated.view.controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"Missing control: {label} {nth}")
  IO.ofExcept ((evaluated.applyKey control.key argument).mapError fun error =>
    toString (ModelForm.Rejection.ofAction error))

mutual
private def texts (label : String) : Display.View → List String
  | .computed name value => if name == label then [value] else []
  | .stack _ children => textsAll label children
  | .list _ children _ => textsAll label children
  | .table _ _ rows footer _ => textsRows label rows ++ texts label footer
  | _ => []

private def textsAll (label : String) : List Display.View → List String
  | [] => []
  | child :: rest => texts label child ++ textsAll label rest

private def textsRows (label : String) : List Display.TableRow → List String
  | [] => []
  | ⟨_, cells, _⟩ :: rest => textsAll label cells ++ textsRows label rest
end

example : True := by
  fail_if_success have bad : CellViews ["Description", "Selected"] := .cons .hidden .nil
  fail_if_success have bad : Columns [] String Unit :=
    ⟨["Description", "Selected"], Unit, .output (.const ())⟩
  trivial

@[expose] def functions : Component [] Nat (Nat → Nat) :=
  .bind (fun n : Nat => n) <|
    .withOutput (.button "Use successor" (.set .here (.const (fun n => n + 1))))
      { inputs := inputs[.ui (Ref.here : Var _ (Nat → Nat))], run := id }

@[expose] def dependent : Component [] Nat Nat :=
  .observe
    (.bind (0 : Nat) <|
      .withOutput (.button "Increment" (.set .here {
        inputs := inputs[.ui (Ref.here : Var _ Nat)], run := fun n => n + 1 }))
        { inputs := inputs[.ui (Ref.here : Var _ Nat), path[]], run := Nat.add })
    (.withOutput (.field .self "Model" .natural) {
      inputs := inputs[.ui (Ref.here : InputRef _ Nat)], run := id })

@[expose] def request (count : Nat) : HttpRequest :=
  { method := .get, url := s!"/count/{count}", body := none }

@[expose] def remote : Component [] Nat Nat :=
  .observe counter <|
    .load {
      inputs := inputs[.ui (Ref.here : InputRef _ Nat)]
      run := fun count => .fetch (request count) (Lean.fromJson? (α := Nat)) }
      (fun status => .output (.const (match status with
        | .ready value => value
        | _ => 0)))

@[expose] def loadedCounter : Component [] Nat Nat :=
  .load (.const (.fetch (request 0) (Lean.fromJson? (α := Nat)))) fun
    | .ready _ => counter
    | _ => .output (.const 0)

def run : IO Unit := do
  let opened := single.evaluate 10 Env.nil
  check "EvaluationReturnsProducerOutput"
    (opened.output == 0 && texts "Observer one" opened.view == ["0"] && texts "Observer two" opened.view == ["Twice: 0"])
  let increment ← press opened "Increment"
  let updated := single.evaluate increment.value increment.state {} increment.locals
  check "EvaluationActionsUpdatePrivateState" (updated.output == 1 && increment.value == 10)
  check "EvaluationIsAFixedSnapshot" (opened.output == 0 && texts "Observer one" opened.view == ["0"])
  let remember ← press updated "Remember output"
  let remembered := single.evaluate remember.value remember.state {} remember.locals
  check "EvaluationConsumerActionsReadReturnedOutput" (texts "Remembered" remembered.view == ["1"])
  let incrementAgain ← press remembered "Increment"
  let latest := single.evaluate incrementAgain.value incrementAgain.state {} incrementAgain.locals
  check "EvaluationRebuildRefreshesOutputs"
    (latest.output == 2 && texts "Observer one" latest.view == ["2"] && texts "Remembered" latest.view == ["1"])
  let changePrivate ← press latest "Change private"
  let privateChanged := single.evaluate changePrivate.value changePrivate.state {} changePrivate.locals
  check "EvaluationKeepsPrivateVariablesPrivate"
    (privateChanged.output == 2 && texts "Private value" privateChanged.view == ["101"])

  let pairs := rows.evaluate [10, 10] Env.nil
  let first ← press pairs "Increment"
  let first := rows.evaluate first.value first.state {} first.locals
  let second ← press first "Increment" 1
  let second := rows.evaluate second.value second.state {} second.locals
  let other ← press second "Increment" 3
  let both := rows.evaluate other.value other.state {} other.locals
  check "EvaluationCollectsNestedRowOutputs"
    (both.output == [2, 1] && texts "Pair sum" both.view == ["2", "1"])
  let removed ← press both "Remove"
  let survivor := rows.evaluate removed.value removed.state {} removed.locals
  check "EvaluationRemovalRetainsSurvivingPrivateState" (removed.value == [10] && survivor.output == [1])
  let added ← press survivor "Add pair"
  let added := rows.evaluate added.value added.state {} added.locals
  check "EvaluationNewRowsStartFresh" (added.output == [1, 0])
  let removeFirst ← press added "Remove"
  let last := rows.evaluate removeFirst.value removeFirst.state {} removeFirst.locals
  let removeLast ← press last "Remove"
  let empty := rows.evaluate removeLast.value removeLast.state {} removeLast.locals
  check "EvaluationCollectsEmptyRows" (empty.output == [])
  let totals := nested.evaluate [10, 10] Env.nil {}
    ⟨⟨both.locals, nested.initialState.producer.consumers⟩, ()⟩
  check "EvaluationObservesCollectedOutputs" (totals.output == 3 && texts "Overall sum" totals.view == ["3"])

  let functional := functions.evaluate 0 Env.nil
  let successor ← press functional "Use successor"
  let functional := functions.evaluate successor.value successor.state {} successor.locals
  check "EvaluationSupportsFunctionOutputs" (functional.output 41 == 42)
  let valueDependent := dependent.evaluate 10 Env.nil
  let modelEdit ← press valueDependent "Model" (argument := some (.text "17"))
  let valueDependent := dependent.evaluate modelEdit.value modelEdit.state {} modelEdit.locals
  let countEdit ← press valueDependent "Increment"
  let valueDependent := dependent.evaluate countEdit.value countEdit.state {} countEdit.locals
  check "EvaluationRefreshesAfterModelAndContextChanges" (valueDependent.output == 18 && countEdit.value == 17)

  let waiting := remote.evaluate 10 Env.nil
  check "EvaluationRequestsUseReturnedOutput" (waiting.requests == [request 0])
  let increment ← press waiting "Increment"
  let waiting := remote.evaluate increment.value increment.state {} increment.locals
  check "EvaluationRequestsRefreshAfterActions" (waiting.requests == [request 1])
  let cache : HttpRequest.Cache := ({} : HttpRequest.Cache).insert (request 1) (.loaded (Lean.toJson (13 : Nat)))
  let ready := remote.evaluate increment.value increment.state cache waiting.locals
  check "EvaluationRefreshesAfterCacheChanges" (ready.output == 13 && waiting.output == 0)

  let initialCache : HttpRequest.Cache := ({} : HttpRequest.Cache).insert (request 0) (.loaded (Lean.toJson (1 : Nat)))
  let loaded := loadedCounter.evaluate 0 Env.nil initialCache
  let increment ← press loaded "Increment"
  let retained := loadedCounter.evaluate increment.value increment.state initialCache increment.locals
  let changedCache := initialCache.insert (request 0) (.loaded (Lean.toJson (2 : Nat)))
  let reset := loadedCounter.evaluate increment.value increment.state changedCache retained.locals
  check "EvaluationLoadedStateRetainsAndResets" (retained.output == 1 && reset.output == 0)

  let status : Component [] Nat (Status Nat) :=
    .load (.const (.fetch (request 0) (Lean.fromJson? (α := Nat)))) fun status =>
      .output (.const status)
  let fixedConsumer : Component [] Nat Nat := .observe status <|
    .bind (0 : Nat) <|
      let count : Var [⟨.writable, Nat⟩, ⟨.readOnly, Status Nat⟩] Nat := .here
      let status : InputRef [⟨.writable, Nat⟩, ⟨.readOnly, Status Nat⟩] (Status Nat) := .there .here
      .withOutput (.button "Increment consumer" (.set count {
        inputs := inputs[.ui count], run := fun n => n + 1 })) {
        inputs := inputs[.ui count, .ui status]
        run := fun count status => count + match status with
          | .ready value => value
          | _ => 0 }
  let waitingConsumer := fixedConsumer.evaluate 0 Env.nil
  let incrementConsumer ← press waitingConsumer "Increment consumer"
  let waitingConsumer := fixedConsumer.evaluate 0 Env.nil {} incrementConsumer.locals
  let readyConsumer := fixedConsumer.evaluate 0 Env.nil initialCache waitingConsumer.locals
  let changedConsumer := fixedConsumer.evaluate 0 Env.nil changedCache readyConsumer.locals
  check "EvaluationReadOnlyStatusKeepsConsumerState"
    (waitingConsumer.output == 1 && readyConsumer.output == 2 && changedConsumer.output == 3)

  let focused : Component [] (List Nat) (Option Nat) :=
    .focus (.const (.index 0 .self)) single
  let focusedFirst := focused.evaluate [10] Env.nil
  let increment ← press focusedFirst "Increment"
  let focusedUpdated := focused.evaluate increment.value increment.state {} increment.locals
  let missing := focused.evaluate [] Env.nil {} focusedUpdated.locals
  check "EvaluationOutputsComposeUnderFocus"
    (focusedUpdated.output == some 1 && missing.output == none && missing.view.controls.isEmpty && missing.requests.isEmpty)

  let outer : Component [] Nat Nat := .bind (0 : Nat) <|
    .observe (.output { inputs := inputs[.ui (Ref.here : Var _ Nat)], run := id })
      (.withOutput (.button "Set outer" (.set (Ref.there Ref.here) (.const 5))) {
        inputs := inputs[.ui (Ref.here : InputRef _ Nat)], run := id })
  let outerFirst := outer.evaluate 0 Env.nil
  let outerEdit ← press outerFirst "Set outer"
  let outerUpdated := outer.evaluate outerEdit.value outerEdit.state {} outerEdit.locals
  check "EvaluationPreservesOuterWritableContext" (outerUpdated.output == 5)

  let table := selectionTable.evaluate ["same", "same"] Env.nil
  check "EvaluationTableStartsWithRowLocalOutputs"
    (table.output == [⟨"same", false⟩, ⟨"same", false⟩])
  let toggle ← press table "Toggle selection"
  let firstSelected := selectionTable.evaluate toggle.value toggle.state {} toggle.locals
  check "EvaluationTableSelectionIsPerRow"
    (firstSelected.output == [⟨"same", true⟩, ⟨"same", false⟩])
  let toggle ← press firstSelected "Toggle selection" 1
  let bothSelected := selectionTable.evaluate toggle.value toggle.state {} toggle.locals
  check "EvaluationTableHandlesRepeatedDescriptions"
    (bothSelected.output == [⟨"same", true⟩, ⟨"same", true⟩])
  let edit ← press bothSelected "Description" (argument := some (.text "Revised"))
  let edited := selectionTable.evaluate edit.value edit.state {} edit.locals
  check "EvaluationColumnOutputsFeedLaterCells"
    (edited.output == [⟨"Revised", true⟩, ⟨"same", true⟩] &&
      texts "Cell description" edited.view == ["Revised", "same"])
  let summary := selectedDescriptions.evaluate edit.value edit.state {}
    ⟨⟨edited.locals, selectedDescriptions.initialState.producer.consumers⟩, ()⟩
  check "EvaluationTableOutputsFeedIndependentSummary"
    (summary.output == "Revised, same" && texts "Selected descriptions" summary.view == ["Revised, same"])
  let remove ← press edited "Remove"
  let remaining := selectionTable.evaluate remove.value remove.state {} remove.locals
  check "EvaluationTableRemovalRetainsCellState" (remaining.output == [⟨"same", true⟩])
  let add ← press remaining "Add item"
  let withNew := selectionTable.evaluate add.value add.state {} add.locals
  check "EvaluationTableNewRowsStartUnselected"
    (withNew.output == [⟨"same", true⟩, ⟨"New item", false⟩])

  let noRows := selectionTable.evaluate [] Env.nil
  check "EvaluationEmptyTableRetainsHeaders" (noRows.output.isEmpty && match noRows.view with
    | .table _ headers rows _ _ => headers == ["Description", "Selected", "Actions"] && rows.isEmpty
    | _ => false)
  check "EvaluationTableCellCountMatchesHeaders" (match withNew.view with
    | .table _ headers rows _ _ => rows.all fun row => row.cells.length == headers.length
    | _ => false)
  check "EvaluationTableSelectionButtonsAreUserDefined" (match withNew.view with
    | .table _ _ rows _ _ => rows.all (·.selected.isNone)
    | _ => false)

  let ordinaryColumns : Columns [] String Unit :=
    .cons "Description" ((.field .self "Description" .text)) .nil
  let ordinary := Component.table .self "Ordinary" "Item" "" ordinaryColumns
  let ordinaryResult := ordinary.evaluate ["one", "two"] Env.nil
  check "EvaluationOrdinaryColumnsReturnUnit" (ordinaryResult.output == [(), ()])

  let rowBound : Columns [] String Bool := .bind false <|
    let selected : Var [⟨.writable, Bool⟩] Bool := .here
    .cons "Selection" ((.button "Row toggle" (.set selected {
      inputs := inputs[.ui selected], run := Bool.not })))
      (.output { inputs := inputs[.ui selected], run := id })
  let rowBoundTable := Component.table .self "Rows" "Row" "" rowBound
  let rowBoundOpened := rowBoundTable.evaluate ["same", "same"] Env.nil
  let rowBoundEdit ← press rowBoundOpened "Row toggle"
  let rowBoundUpdated := rowBoundTable.evaluate rowBoundEdit.value rowBoundEdit.state {} rowBoundEdit.locals
  check "EvaluationColumnsCanOwnRowLocalVariables" (rowBoundUpdated.output == [true, false])

  let focusedColumns : Columns [] (List String) (Option RowOutput) :=
    .focus (.const (.index 0 .self)) selectionColumns
  let focusedTable := Component.table .self "Rows" "Row" [] focusedColumns
  let focused := focusedTable.evaluate [["same"]] Env.nil
  let toggle ← press focused "Toggle selection"
  let focused := focusedTable.evaluate toggle.value toggle.state {} toggle.locals
  check "EvaluationFocusedColumnsKeepRowLocalState"
    (focused.output == [some ⟨"same", true⟩])
  let edit ← press focused "Description" (argument := some (.text "Revised"))
  let focused := focusedTable.evaluate edit.value edit.state {} edit.locals
  check "EvaluationFocusedColumnsEditNestedRows"
    (edit.value == [["Revised"]] && focused.output == [some ⟨"Revised", true⟩])
  let unfocused := focusedTable.evaluate [[]] Env.nil
  check "EvaluationMissingFocusKeepsTableColumns" (unfocused.output == [none] && match unfocused.view with
    | .table _ headers rows _ _ => headers == ["Description", "Selected", "Actions"] &&
        rows.all fun row => row.cells.length == headers.length
    | _ => false)

  let remoteColumns : Columns [] String Nat := Columns.observe "Description" descriptionCell <|
    Columns.observe "Remote"
      (.load {
        inputs := inputs[.ui (Ref.here : InputRef _ String)]
        run := fun description => .fetch { method := .get, url := s!"/row/{description}", body := none }
          (Lean.fromJson? (α := Nat)) }
        (fun status => .output (.const (match status with
          | .ready value => value
          | _ => 0))))
      (.output { inputs := inputs[.ui (Ref.here : InputRef _ Nat)], run := id })
  let remoteTable := Component.table .self "Rows" "Row" "" remoteColumns
  let remoteRows := remoteTable.evaluate ["one", "two"] Env.nil
  check "EvaluationColumnRequestsUseEarlierCellOutputs"
    (remoteRows.requests.map (·.url) == ["/row/one", "/row/two"] && remoteRows.output == [0, 0])
  let some firstRequest := remoteRows.requests.head? | throw (IO.userError "Missing row request")
  let rowCache := ({} : HttpRequest.Cache).insert firstRequest (.loaded (Lean.toJson (21 : Nat)))
  let loadedRows := remoteTable.evaluate ["one", "two"] Env.nil rowCache remoteRows.locals
  check "EvaluationColumnOutputsRefreshAfterLoading" (loadedRows.output == [21, 0])

  let hiddenProducer : Component [] Nat Nat := Component.visibleWhen (.const false) <|
    .withOutput (.group "Hidden" [
      .computed "Hidden value" { inputs := inputs[path[]], run := toString },
      .load (.const (.fetch (request 0) (Lean.fromJson? (α := Nat))))
        (fun _ => .computed "Status" (.const "waiting"))])
      { inputs := inputs[path[]], run := id }
  let hiddenObserver : Component [] Nat Nat := .observe hiddenProducer <|
    .withOutput (.computed "Observed hidden value" {
      inputs := inputs[.ui (Ref.here : InputRef _ Nat)], run := toString }) {
      inputs := inputs[.ui (Ref.here : InputRef _ Nat)], run := id }
  let hiddenFirst := hiddenObserver.evaluate 17 Env.nil
  let hiddenChanged := hiddenObserver.evaluate 23 Env.nil {} hiddenFirst.locals
  check "HiddenComponentsKeepOutputsFresh"
    (hiddenFirst.output == 17 && hiddenChanged.output == 23 &&
      texts "Hidden value" hiddenChanged.view == [] && texts "Observed hidden value" hiddenChanged.view == ["23"])
  check "HiddenComponentsSuppressRequests" hiddenChanged.requests.isEmpty
  let labeled := (Component.labeled "Counter result" counter).evaluate 0 Env.nil
  let labeledEdit ← press labeled "Increment"
  let labeled := (Component.labeled "Counter result" counter).evaluate 0 Env.nil {} labeledEdit.locals
  check "GroupLabelsPreserveOutputs" (labeled.output == 1 && labeled.view.title == "Counter result")

end Tests.OutputEvaluation
