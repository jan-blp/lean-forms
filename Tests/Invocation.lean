module

public import Forms.ExampleForms.Registry

public section
namespace Tests.Invocation
open Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private def argument : Display.Editor → Option Input
  | .text _ => some (.text "x")
  | .natural _ => some (.text "1")
  | .checkbox value => some (.boolean !value)
  | .choice selected _ => some (.text selected)
  | .action => none

private def keyOf
  {raw : Type}
  (form : Component [] raw)
  (value : raw)
  (label : String)
  (nth : Nat := 0)
  : ControlKey :=
  let controls := (ModelView.render form value {} [] Env.nil).controls.filter (·.label == label)
  (controls[nth]?.map (·.key)).getD ⟨"missing"⟩

private def perform
  {raw : Type}
  (form : Component [] raw)
  (value : raw)
  (key : ControlKey)
  (argument : Option Input)
  : Except ModelForm.Rejection raw := do
  let invocation ← (ModelView.decodeKey form {} value key argument Env.nil).mapError .ofAction
  return (form.applyValid {} value Env.nil form.initialState invocation).value

private def rejected
  {raw : Type}
  (form : Component [] raw)
  (value : raw)
  (key : ControlKey)
  (argument : Option Input)
  : Option ModelForm.Rejection :=
  match perform form value key argument with
  | .ok _ => none
  | .error rejection => some rejection

private def stale (error : InvocationError) : Option ModelForm.Rejection :=
  some (.stale (.invocation error))

private def clientBug (error : ClientBug) : Option ModelForm.Rejection :=
  some (.clientBug error)

/-- Every control `render` emits decodes and applies to the value it was rendered from. -/
private def everyControlApplies {raw : Type} (form : Component [] raw) (value : raw) : Bool :=
  (ModelView.render form value {} [] Env.nil).controls.all fun control =>
    (perform form value control.key (argument control.input)).toBool

def run : IO Unit := do
  check "InvocationPersonControls" (everyControlApplies Person.form ⟨"Ada", 20, true, ⟨"Lambda Lane"⟩⟩)
  check "InvocationOrderControls" (everyControlApplies Order.form Order.initial)
  check "InvocationExpensesControls" (everyControlApplies ExpenseReport.listForm ExpenseReport.initial)
  check "InvocationTableControls" (everyControlApplies ExpenseReport.form ExpenseReport.initial)
  let street := keyOf Person.form ⟨"Ada", 20, true, ⟨"Lambda Lane"⟩⟩ "Street"
  check "InvocationEdit"
    ((perform Person.form ⟨"Ada", 20, true, ⟨"Lambda Lane"⟩⟩ street (some (.text "Road"))).toOption.map (·.address.street)
      == some "Road")
  check "InvocationHidden"
    (rejected Person.form Person.initial street (some (.text "Road")) == stale .absent)
  let manyItems := { Order.initial with quantity := 11 }
  check "InvocationDisabled"
    (rejected Order.form manyItems (keyOf Order.form manyItems "Gift wrap") (some (.boolean true))
      == stale .disabled)
  check "InvocationMissingArgument"
    (rejected Person.form Person.initial (keyOf Person.form Person.initial "Age") none
      == clientBug .missingArgument)
  check "InvocationInvalidArgument"
    (rejected Person.form Person.initial (keyOf Person.form Person.initial "Age") (some (.text "abc"))
      == some (.input "Enter a non-negative whole number."))
  check "InvocationUnknownKey"
    (rejected Person.form Person.initial ⟨"missing"⟩ none == stale .absent)
  check "InvocationWrongArgument"
    (rejected Person.form Person.initial (keyOf Person.form Person.initial "Age") (some (.boolean true))
      == clientBug (.wrongArgument "text"))
  let opened := ModelForm.openState Person.form Person.initial Env.nil
  let age := keyOf Person.form Person.initial "Age"
  check "EventInputRejects"
    ((ModelForm.event (model := Person) Person.form opened (.apply age (some (.text "abc")))).toOption.bind
      (·.ui.rejection) == some "Enter a non-negative whole number.")
  check "EventStaleRejects"
    ((ModelForm.event (model := Person) Person.form opened (.apply street (some (.text "Road")))).toOption.bind
      (·.ui.rejection) == some (toString InvocationError.absent))
  check "EventProtocolFails"
    !(ModelForm.event (model := Person) Person.form opened (.apply age none)).toBool
  let shipping := keyOf Order.form Order.initial "Shipping"
  check "InvocationUnavailableBranch"
    (rejected Order.form Order.initial shipping (some (.text "drone"))
      == stale (.unavailableBranch "drone"))
  match perform Order.form Order.initial shipping (some (.text "express")) with
  | .error rejection => throw (IO.userError s!"FAIL InvocationSelect: {rejection}")
  | .ok express =>
    let phone := keyOf Order.form express "Phone"
    check "InvocationSelectedBranchEdits" (perform Order.form express phone (some (.text "1"))).toBool
    check "InvocationInactiveBranch"
      (rejected Order.form Order.initial phone (some (.text "1")) == stale .absent)
    check "InvocationReselectKeeps"
      ((perform Order.form express shipping (some (.text "express"))).toOption.map Lean.toJson
        == some (Lean.toJson express))
  let add := keyOf ExpenseReport.listForm ExpenseReport.initial "Add expense"
  check "InvocationUnexpectedArgument"
    (rejected ExpenseReport.listForm ExpenseReport.initial add (some (.text "x"))
      == clientBug .unexpectedArgument)
  match perform ExpenseReport.listForm ExpenseReport.initial add none with
  | .error rejection => throw (IO.userError s!"FAIL InvocationAdd: {rejection}")
  | .ok longer =>
    check "InvocationAdd" (longer.expenses.length == ExpenseReport.initial.expenses.length + 1)
    let removeLast := keyOf ExpenseReport.listForm longer "Remove" ExpenseReport.initial.expenses.length
    check "InvocationMissingItem"
      (rejected ExpenseReport.listForm ExpenseReport.initial removeLast none == stale .absent)

end Tests.Invocation
