module

public import Forms.ExampleForms.Presentation
public import Forms.Runtime.ModelForm
public import Forms.Runtime.ControlKeyProtocol

public section
namespace Tests.Presentation
open Forms.Model Forms.Runtime Forms.Runtime.ModelView
open Forms.ExampleForms.Presentation

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

-- A layout can only place components its own presentation has already taken ownership of.
example : True := by
  fail_if_success have bad : Presentation 0 [] Nat := .arrange (.const (.place .here))
  fail_if_success
    have bad : Presentation 1 [⟨.readOnly, Unit⟩] Nat := .arrange (.const (.place (.there .here)))
  trivial

-- A nested presentation cannot place components owned by an enclosing one.
example : True := by
  let field : Component [] Nat := .field .self "Count" .natural
  have _ : Component [] Nat := .present (.own field (.arrange (.const (.place .here))))
  fail_if_success
    have bad : Component [] Nat :=
      .present (.own field (.own (.present (.arrange (.const (.place .here))))
        (.arrange (.const (.place .here)))))
  trivial

private def control
  {α state β : Type}
  (evaluated : Evaluated [] α state β)
  (label : String)
  (nth : Nat := 0)
  : IO Display.Control := do
  let some found := (evaluated.view.controls.filter (·.label == label))[nth]?
    | throw (IO.userError s!"Missing control: {label} {nth}")
  return found

private def press
  {α β : Type}
  (component : Component [] α β)
  (evaluated : Evaluated [] α component.LocalState β)
  (label : String)
  (nth : Nat := 0)
  (argument : Option Input := none)
  : IO (Evaluated [] α component.LocalState β) := do
  let control ← control evaluated label nth
  let updated ← IO.ofExcept ((evaluated.applyKey control.key argument).mapError fun error =>
    toString (ModelForm.Rejection.ofAction error))
  return component.evaluate updated.value updated.state {} updated.locals

private def tab
  {α β : Type}
  (component : Component [] α β)
  (evaluated : Evaluated [] α component.LocalState β)
  (bar : String)
  (index : Nat)
  (nth : Nat := 0)
  : IO (Evaluated [] α component.LocalState β) :=
  press component evaluated bar nth (some (.text (toString index)))

mutual
private def texts (label : String) : Display.View → List String
  | .computed name value => if name == label then [value] else []
  | .stack _ children => textsAll label children
  | .list (children := children) .. => textsAll label children
  | .table (rows := rows) (footer := footer) .. => textsRows label rows ++ texts label footer
  | _ => []

private def textsAll (label : String) : List Display.View → List String
  | [] => []
  | child :: rest => texts label child ++ textsAll label rest

private def textsRows (label : String) : List Display.TableRow → List String
  | [] => []
  | { cells, .. } :: rest => textsAll label cells ++ textsRows label rest
end

/-- Computed labels and tables in display order. -/
private partial def order : Display.View → List String
  | .computed name _ => [name]
  | .table label .. => [label]
  | .stack _ children => children.flatMap order
  | .list (children := children) .. => children.flatMap order
  | _ => []

def request : HttpRequest := { method := .get, url := "/hidden-value", body := none }

@[expose] def unplaced : Component [] Nat Nat :=
  .present <|
    .own (Component.load
      (.const (.fetch request (Lean.fromJson? (α := Nat))))
      (fun status => .output (.const (match status with
        | .ready value => value
        | _ => 0)))) <|
      .layout { inputs := inputs[.ui (Ref.here : InputRef _ Nat)], run := id } (.const (.group none []))

def run : IO Unit := do
  let initial := ["same", "same", "other"]
  let opened := (tableSummary).evaluate initial Env.nil
  check "PresentationSummaryPrecedesItsProducer"
    (order opened.view == ["Selected descriptions", "Items"] && opened.output == "")
  let selected ← press tableSummary opened "Toggle selection" 1
  check "PresentationSummaryReadsRowLocalOutput"
    (selected.output == "same" && texts "Selected descriptions" selected.view == ["same"])
  let field ← control selected "Description" 1
  let tableLast ← control selected "Toggle selection" 1
  let reversed := (tableSummary tableAbove).evaluate initial Env.nil {} selected.locals
  let tableFirst ← control reversed "Toggle selection" 1
  check "PresentationReorderingPreservesStateAndActionIdentity"
    (reversed.output == "same" && tableFirst == tableLast &&
      order reversed.view == ["Items", "Selected descriptions"])
  let edited ← press (tableSummary tableAbove) reversed "Description" 1 (some (.text "Revised"))
  check "PresentationReorderedActionsReachTheirOwner"
    (edited.output == "Revised" && texts "Cell description" edited.view == ["same", "Revised", "other"])

  let regrouped := (tableSummary (.group (some "New grouping") [
    .group (some "Summary") [.place .here],
    .group (some "Editor") [.place (.there .here)]])).evaluate edited.value Env.nil {} edited.locals
  check "PresentationRegroupingKeepsOwnershipRoutes"
    ((← control regrouped "Toggle selection" 1) == tableLast)
  let summaryOnly := (tableSummary (.place .here)).evaluate edited.value Env.nil {} edited.locals
  check "PresentationUnplacedControlsRejectStaleActions"
    (summaryOnly.view.controls.isEmpty && !(summaryOnly.applyKey tableLast.key).toBool)
  let refreshed := (tableSummary (.place .here)).evaluate ["same", "Fresh", "other"] Env.nil {} edited.locals
  check "PresentationUnplacedOwnersStillProduceFreshOutputs"
    (refreshed.output == "Fresh" && texts "Selected descriptions" refreshed.view == ["Fresh"])
  let duplicate : Layout 2 := .group none [.place (.there .here), .place (.there .here), .place .here]
  let duplicated := (tableSummary duplicate).evaluate edited.value Env.nil {} edited.locals
  check "PresentationDuplicatePlacementKeepsOneEditableControl"
    (duplicated.view.controls.length == edited.view.controls.length)
  let errors : List Feedback.Error := [⟨"Review this item", .locations [.index 1] []⟩]
  let feedback := regrouped.feedback errors
  let some described := (feedback.controls.filter (·.label == "Description"))[1]?
    | throw (IO.userError "Missing described control")
  check "PresentationValidationFollowsTheOwner"
    (described.messages == some "Review this item" && described.target == field.target)

  let tabs := sharedTabs.evaluate 0 Env.nil
  check "PresentationTabsOwnAllPanes" (texts "Shared count" tabs.view == ["0"])
  let tabs ← press sharedTabs tabs "Increment shared"
  let tabs ← press sharedTabs tabs "Increment private"
  let firstPrivate ← control tabs "Increment private"
  let tabs ← tab sharedTabs tabs "Panes" 1
  check "PresentationTabsShareStateAndKeepPrivateStateSeparate"
    (tabs.output == 1 && texts "Shared count" tabs.view == ["1"] && texts "Private count" tabs.view == ["0"])
  check "PresentationInactiveTabRejectsStaleActions"
    (!(tabs.applyKey firstPrivate.key).toBool)
  let tabs ← press sharedTabs tabs "Increment shared"
  let tabs ← press sharedTabs tabs "Increment private"
  let tabs ← press sharedTabs tabs "Increment private"
  let tabs ← tab sharedTabs tabs "Panes" 0
  check "PresentationReturningToTabRetainsPrivateState"
    (tabs.output == 2 && texts "Private count" tabs.view == ["1"] &&
      (← control tabs "Increment private") == firstPrivate)
  let tabs ← tab sharedTabs tabs "Panes" 1
  check "PresentationOtherTabRetainsItsOwnPrivateState"
    (texts "Private count" tabs.view == ["2"])
  let bar ← control tabs "Panes"
  check "TabBarShowsTheActiveTab" (bar.input == .tabs 1 ["First pane", "Second pane"])
  check "TabBarRejectsMissingTabs" (!(tabs.applyKey bar.key (some (.text "2"))).toBool)
  check "TabBarKeyRoundTrips"
    (match ControlKeyProtocol.fromString (ControlKeyProtocol.toString bar.key) with
      | .ok key => key == bar.key
      | .error _ => false)

  let pending := unplaced.evaluate 0 Env.nil
  check "PresentationPlacementDoesNotSuppressOwnedRequests"
    (pending.requests == [request] && pending.view.controls.isEmpty && pending.output == 0)
  let cache := ({} : HttpRequest.Cache).insert request (.loaded (Lean.toJson (7 : Nat)))
  let loaded := unplaced.evaluate 0 Env.nil cache pending.locals
  check "PresentationUnplacedLoadUpdatesItsOutput" (loaded.output == 7)

  let opened := notes.evaluate ["a", "b"] Env.nil
  check "NestedPresentationsRenderInsideTheirOwner"
    (opened.output == 2 && order opened.view == ["Note count"] &&
      (opened.view.controls.filter (·.label == "Text")).length == 2)
  let preview ← tab notes opened "Note view" 1 1
  check "NestedRowsKeepIndependentTabs"
    (texts "Preview" preview.view == ["«b»"] &&
      (preview.view.controls.filter (·.label == "Text")).length == 1)
  let edited ← press notes preview "Text" 0 (some (.text "x"))
  check "NestedRowActionsReachTheirRow"
    (edited.value == ["x", "b"] && texts "Preview" edited.view == ["«b»"])
  let removed ← press notes edited "Remove" 0
  check "NestedRowRemovalKeepsRemainingRowState"
    (removed.value == ["b"] && removed.output == 1 && texts "Preview" removed.view == ["«b»"] &&
      (removed.view.controls.filter (·.label == "Text")).isEmpty)
  let added ← press notes removed "Add note"
  check "NestedNewRowsStartOnTheirFirstTab"
    (added.value == ["b", ""] && texts "Preview" added.view == ["«b»"] &&
      (added.view.controls.filter (·.label == "Text")).length == 1)

end Tests.Presentation
