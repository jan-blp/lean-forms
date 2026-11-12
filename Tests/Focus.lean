module

public import Forms.ExampleForms.Registry
meta import Forms.Model.PartialPath.Theorems

public section
namespace Tests.Focus
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private def perform
  {Γ : List Type}
  {raw : Type}
  (form : Component Γ raw)
  (current : raw)
  (key : ControlKey)
  (argument : Option Input)
  (state : Env Γ)
  : Except ModelForm.Rejection raw := do
  let invocation ← (ModelView.decodeKey form {} current key argument state).mapError .ofAction
  return (form.applyValid {} current state form.initialState invocation).value

private def firstControl
  {Γ : List Type}
  {raw : Type}
  (form : Component Γ raw)
  (value : raw)
  (state : Env Γ)
  : IO Display.Control := do
  let some control := (ModelView.render form value {} [] state).controls.head?
    | throw (IO.userError "FAIL missing focused control")
  return control

private def street : Component [] Address.Raw :=
  .field path[Address.Field.street] "Street" .text

def run : IO Unit := do
  let person := Person.initial
  let focused : Component [] Person.Raw := .focus
    (.const (.ofPath path[Person.Field.address])) street
  let direct : Component [] Person.Raw :=
    .field path[Person.Field.address, Address.Field.street] "Street" .text
  let control ← firstControl focused person Env.nil
  let directControl ← firstControl direct person Env.nil
  check "FocusUsesModelLocation"
    (control.key == directControl.key && control.location == [.field "address", .field "street"])
  let updated ← IO.ofExcept ((perform focused person control.key (some (.text "Main")) Env.nil).mapError toString)
  check "FocusWritesNestedValue"
    (updated.address.street == "Main" && updated.name == person.name && updated.age == person.age)
  let nested : Component [] Person.Raw := .focus (.const (.ofPath path[Person.Field.address]))
    (.focus (.const (.ofPath path[Address.Field.street])) (.field .self "Street" .text))
  let nestedControl ← firstControl nested person Env.nil
  check "FocusComposes" (nestedControl.key == control.key && nestedControl.location == control.location)
  let disabled := Component.disabledWhen (.const true) focused
  check "FocusHonorsDisabled"
    (match perform disabled person control.key (some (.text "Blocked")) Env.nil with
    | .error (.stale (.invocation .disabled)) => true
    | _ => false)
  let outOfBounds : PartialPath ExpenseReport.Raw Expense.Raw :=
    (PartialPath.ofPath path[ExpenseReport.Field.expenses]).trans (.index 99 .self)
  let absent : Component [] ExpenseReport.Raw := .focus (.const outOfBounds)
    (.field path[Expense.Field.description] "Description" .text)
  check "FocusMissingIndexIsHidden"
    ((ModelView.render absent ExpenseReport.initial {} [] Env.nil).view == .hidden &&
      toJson (outOfBounds.set ⟨"Ignored", 1, false⟩ ExpenseReport.initial) == toJson ExpenseReport.initial)
  let phonePath : PartialPath Shipping.Raw String :=
    .constructor Shipping.Constructor.express (.ofPath path[Shipping.express.Field.phone])
  let phone : Component [] Shipping.Raw := .focus (.const phonePath) (.field .self "Phone" .text)
  check "FocusInactiveConstructorIsHidden"
    ((ModelView.render phone .pickup {} [] Env.nil).controls.isEmpty && phonePath.get? .pickup == none &&
      toJson (phonePath.set "Ignored" .pickup) == toJson Shipping.Raw.pickup)
  let express : Shipping.Raw := .express ⟨⟨"Main", "Bern"⟩, ""⟩
  let phoneControl ← firstControl phone express Env.nil
  check "FocusConstructorLocation"
    (phoneControl.location == [.constructor "express", .field "phone"])
  let changed ← IO.ofExcept ((perform phone express phoneControl.key (some (.text "079")) Env.nil).mapError toString)
  check "FocusWritesConstructorPayload" (toJson changed == toJson (Shipping.Raw.express ⟨⟨"Main", "Bern"⟩, "079"⟩))
  let invalid := { ModelForm.openState phone express Env.nil with validationStarted := true }
  let snapshot := ModelForm.snapshot (model := Shipping) phone invalid
  check "FocusMatchesValidationMessages"
    (snapshot.controls.head?.bind (·.messages) == some "Enter a phone number for the courier.")
  -- A selected-item focus works by itself, with no table in the component tree.
  let details : Component [RowSelection] ExpenseReport.Raw := .focus
    { inputs := inputs[.ui (Var.here : Var [RowSelection] RowSelection)]
      run := RowSelection.itemPath path[ExpenseReport.Field.expenses] }
    (.field path[Expense.Field.description] "Description" .text)
  let selected := ExpenseReport.initial
  let selectedUi : Env [RowSelection] := env[.row 1]
  let detail ← firstControl details selected selectedUi
  let edited ← IO.ofExcept ((perform details selected detail.key (some (.text "Independent")) selectedUi).mapError toString)
  check "FocusIndependentOfTable"
    (edited.expenses.map (·.description) == ["Train to Bern", "Independent"] &&
      edited.employee == selected.employee)
  let invalidValue : ExpenseReport.Raw := { selected with
    expenses := [⟨"Train to Bern", 58, false⟩, ⟨"", 180, true⟩] }
  let invalidState := { ModelForm.openState details invalidValue selectedUi with
    validationStarted := true }
  let invalidDetails := ModelForm.snapshot (model := ExpenseReport) details invalidState
  check "FocusListValidationLocation"
    (invalidDetails.controls.head?.bind (·.messages) == some "Describe the expense." &&
      detail.location == [.field "expenses", .index 1, .field "description"])
  let moved : Component [RowSelection] ExpenseReport.Raw := .group "Elsewhere" [
    .computed "Summary" (.const "Summary"), .group "Details" [details]]
  let movedControl ← firstControl moved selected selectedUi
  let movedEdit ← IO.ofExcept ((perform moved selected detail.key (some (.text "Moved")) selectedUi).mapError toString)
  check "FocusKeySurvivesLayoutChange"
    (movedControl.key == detail.key && movedEdit.expenses.map (·.description) == ["Train to Bern", "Moved"])

end Tests.Focus
