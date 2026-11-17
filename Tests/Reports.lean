module

public import Forms.ExampleForms.PaymentMethod
public import Forms.Runtime.ModelForm
public import Tests.FreshId
meta import Forms.Model.Derive

public section
namespace Tests.Reports
open Forms.Model Forms.Runtime Forms.ExampleForms

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

structure Payments where
  primary : Option PaymentMethod
  others : List (Item PaymentMethod)
  deriving FormModel

@[report_rule] structure Flagged where
  note : String
  deriving FormModel

/-- error: deriving FormModel for `Tests.Reports.UsesFlagged`: reports: Reports Flagged is missing: declare its report rule before deriving Tests.Reports.UsesFlagged -/
#guard_msgs in
structure UsesFlagged where
  flagged : Flagged
  deriving FormModel

private def nested : Payments.Raw where
  primary := some PaymentMethod.initial
  others := [⟨firstId, PaymentMethod.initial⟩]

example : (ModelForm.reports (model := Payments) nested).map (·.targets) = [
    .locations [.field "primary", .constructor "some", .field "value"] [],
    .locations [.field "others", .item firstId, .field "value", .field "value"] []] := by
  decide

private def label : String := "Expense Payment Method"

private def messages (state : ModelForm.State PaymentMethod.form) : List Message :=
  ((state.evaluation.view.controls.find? (·.label == label)).map (·.messages)).getD []

def run : IO Unit := do
  let opened := ModelForm.openState (model := PaymentMethod) (supply := supply) PaymentMethod.form
    PaymentMethod.initial Env.nil
  let failing := [{ kind := .report, text := "The payment method does not match the receipt." }]
  check "ReportsShowFailingChecksOnTheirTarget" (messages opened == failing)
  let some control := opened.evaluation.view.controls.find? (·.label == label)
    | throw (IO.userError s!"Missing control: {label}")
  let cleared ← IO.ofExcept (ModelForm.execute (model := PaymentMethod) PaymentMethod.form opened
    (.apply control.key (some (.text "none"))))
  check "ReportsSurviveEdits" (cleared.value.value == none && messages cleared == failing)
  check "ReportsDoNotBlockSubmit" ((ModelForm.submit cleared).outbox.contains .submit)

end Tests.Reports
