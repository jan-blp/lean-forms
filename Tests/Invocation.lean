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
  (form : Component raw)
  (value : raw)
  (label : String)
  (nth : Nat := 0)
  : ControlKey :=
  let controls := (ModelView.render form value {}).controls.filter (·.label == label)
  (controls[nth]?.map (·.key)).getD ⟨"missing"⟩

private def perform
  {raw : Type}
  (form : Component raw)
  (value : raw)
  (key : ControlKey)
  (argument : Option Input)
  : Except ModelForm.Rejection raw := do
  let invocation ← (ModelView.decodeKey form key argument).mapError .ofDecode
  (form.apply {} value invocation).mapError fun error => .stale (.invocation error)

private def rejected
  {raw : Type}
  (form : Component raw)
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
private def everyControlApplies {raw : Type} (form : Component raw) (value : raw) : Bool :=
  (ModelView.render form value {}).controls.all fun control =>
    (perform form value control.key (argument control.input)).toBool

def run : IO Unit := do
  check "InvocationPersonControls" (everyControlApplies Person.form ⟨"Ada", 20, true, ⟨"Lambda Lane"⟩⟩)
  check "InvocationOrderControls" (everyControlApplies Order.form Order.initial)
  check "InvocationExpensesControls" (everyControlApplies ExpenseReport.form ExpenseReport.initial)
  let street := keyOf Person.form ⟨"Ada", 20, true, ⟨"Lambda Lane"⟩⟩ "Street"
  check "InvocationEdit"
    ((perform Person.form ⟨"Ada", 20, true, ⟨"Lambda Lane"⟩⟩ street (some (.text "Road"))).toOption.map (·.address.street)
      == some "Road")
  check "InvocationHidden"
    (rejected Person.form Person.initial street (some (.text "Road")) == stale .hidden)
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
  check "InvocationUnknownControl"
    (rejected Person.form Person.initial ⟨"[99]"⟩ none == clientBug .unknownControl)
  check "InvocationMalformedKey"
    (rejected Person.form Person.initial ⟨"missing"⟩ none == clientBug .unknownControl)
  check "InvocationWrongArgument"
    (rejected Person.form Person.initial (keyOf Person.form Person.initial "Age") (some (.boolean true))
      == clientBug (.wrongArgument "text"))
  let opened := ModelForm.openState Person.initial
  let age := keyOf Person.form Person.initial "Age"
  check "EventInputRejects"
    ((ModelForm.event (model := Person) Person.form opened (.apply age (some (.text "abc")))).toOption.bind
      (·.ui.rejection) == some "Enter a non-negative whole number.")
  check "EventStaleRejects"
    ((ModelForm.event (model := Person) Person.form opened (.apply street (some (.text "Road")))).toOption.bind
      (·.ui.rejection) == some (toString InvocationError.hidden))
  check "EventProtocolFails"
    !(ModelForm.event (model := Person) Person.form opened (.apply age none)).toBool
  let shipping := keyOf Order.form Order.initial "Shipping"
  check "InvocationUnknownOption"
    (rejected Order.form Order.initial shipping (some (.text "drone"))
      == clientBug .unknownOption)
  match perform Order.form Order.initial shipping (some (.text "express")) with
  | .error rejection => throw (IO.userError s!"FAIL InvocationSelect: {rejection}")
  | .ok express =>
    let phone := keyOf Order.form express "Phone"
    check "InvocationSelectedBranchEdits" (perform Order.form express phone (some (.text "1"))).toBool
    check "InvocationInactiveBranch"
      (rejected Order.form Order.initial phone (some (.text "1")) == stale .inactiveBranch)
    check "InvocationReselectKeeps"
      ((perform Order.form express shipping (some (.text "express"))).toOption.map Lean.toJson
        == some (Lean.toJson express))
  let add := keyOf ExpenseReport.form ExpenseReport.initial "Add expense"
  check "InvocationUnexpectedArgument"
    (rejected ExpenseReport.form ExpenseReport.initial add (some (.text "x"))
      == clientBug .unexpectedArgument)
  match perform ExpenseReport.form ExpenseReport.initial add none with
  | .error rejection => throw (IO.userError s!"FAIL InvocationAdd: {rejection}")
  | .ok longer =>
    check "InvocationAdd" (longer.expenses.length == ExpenseReport.initial.expenses.length + 1)
    let removeLast := keyOf ExpenseReport.form longer "Remove" ExpenseReport.initial.expenses.length
    check "InvocationIndexOutOfBounds"
      (rejected ExpenseReport.form ExpenseReport.initial removeLast none
        == stale (.indexOutOfBounds 2 2))

end Tests.Invocation
