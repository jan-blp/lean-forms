module

public import Forms.ExampleForms.PaymentMethod.Server
public import Forms.ExampleForms.Receipts
public import Forms.Runtime.ModelForm
public import Forms.Runtime.ModelProtocol
public import Forms.Runtime.ReactView
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

private def primary : Diagnostic.Targets :=
  .locations [.field "primary", .constructor "some", .field "value"] []

private def other : Diagnostic.Targets :=
  .locations [.field "others", .item firstId, .field "value", .field "value"] []

example : (ModelForm.reports (model := Payments) nested true).map (·.targets) =
    [primary, primary, other, other] := by
  decide

private def warning (state : Diagnostic.ReportState) (outdated : Bool) : Diagnostic.ReportKind :=
  { state, severity := .warning, outdated }

private def info (state : Diagnostic.ReportState) (outdated : Bool) : Diagnostic.ReportKind :=
  { state, severity := .info, outdated }

private def claimed : Receipts.Raw :=
  ⟨[⟨firstId, "R-1", ⟨true⟩⟩, ⟨secondId, "R-2", ⟨false⟩⟩]⟩

example : (ModelForm.reports (model := Receipts) claimed false).map (·.kind) =
    [.report (warning .unresolved true)] := by
  decide

example : (ModelForm.reports (model := Receipts) claimed true).map (·.kind) =
    [.report (warning .unresolved false)] := by
  decide

example : (Diagnostic.issues [
    { kind := .report (warning .resolved false), message := "resolved", targets := .global },
    { kind := .report (warning .resolved true), message := "passed before", targets := .global },
    { kind := .report (warning .unresolved true), message := "failed before", targets := .global },
    { kind := .report (warning .unresolved false), message := "unresolved", targets := .global },
    { kind := .report (info .unresolved false), message := "optional", targets := .global },
    { kind := .error, message := "error", targets := .global }] []).map (·.message) =
    ["failed before", "unresolved", "error"] := by
  decide

example : Message.checks [
    { kind := .error, text := "error" },
    { kind := .report (warning .unresolved false), text := "open" }] =
    [{ kind := warning .unresolved false, text := "open" }] := by
  decide

example : FormsReact.Checks.of [
    { kind := info .unresolved false, text := "optional" },
    { kind := warning .resolved false, text := "resolved" }] =
    some
      { tone := .resolved
        unresolved := []
        outdated := []
        resolved := ["resolved"]
        optional := ["optional"]
        outdatedOptional := [] } := by
  decide

example : FormsReact.Checks.of [
    { kind := info .unresolved true, text := "optional" },
    { kind := warning .unresolved true, text := "warning" }] =
    some
      { tone := .outdated
        unresolved := []
        outdated := ["warning"]
        resolved := []
        optional := []
        outdatedOptional := ["optional"] } := by
  decide

example : (FormsReact.Checks.of [{ kind := info .unresolved false, text := "optional" }]).map
    (·.tone) = some .optional := by
  decide

private def label : String := "Expense Payment Method"

private partial def markersOf : Display.View → List (List Check)
  | .marker checks => [checks]
  | .stack _ children => children.flatMap markersOf
  | .list (children := children) .. => children.flatMap markersOf
  | .table (rows := rows) (footer := footer) .. =>
    rows.flatMap (·.cells.flatMap markersOf) ++ markersOf footer
  | .keyed _ body => markersOf body
  | .control _ => []
  | .computed .. => []
  | .hidden => []

private def markers (state : ModelForm.State PaymentMethod.form) : List (List Check) :=
  markersOf state.evaluation.view

/-- The saved `value` field's JSON, `none` when the response is not a success. -/
private def savedField? (body : String) : Option Lean.Json :=
  match ModelForm.SubmitOutcome.ofSuccess (α := PaymentMethod.Raw) body with
  | .accepted saved => some (Lean.toJson saved.value)
  | .rejected _ => none
  | .unreachable _ => none

def run : IO Unit := do
  let body := (Lean.toJson ({ value := PaymentMethod.initial } : Saved PaymentMethod.Raw)).compress
  check "SuccessBodyIsTheSavedDocument"
    (savedField? body == some (Lean.toJson PaymentMethod.initial.value))
  check "EmptySuccessIsReported" (savedField? "" == none)
  check "UnreadableSuccessIsReported" (savedField? "{" == none)
  let rejected : Feedback.ServerError := .validation
    { message := "Choose a payment method.", targets := .locations [.field "value"] [] } []
  let decoded := FeedbackProtocol.serverError? (Lean.toJson rejected).compress
  check "ServerErrorsRoundTrip" (decoded.map (·.errors) == some rejected.errors)
  let opened := ModelForm.openState (model := PaymentMethod) (supply := supply) PaymentMethod.form
    PaymentMethod.initial Env.nil
  let mismatch := "The payment method does not match the receipt."
  let receipt : Check :=
    { kind := info .unresolved false, text := PaymentMethod.receiptCheck.message }
  check "MarkerShowsTheFieldChecks"
    (markers opened == [[{ kind := warning .unresolved false, text := mismatch }, receipt]])
  let matching := ModelForm.openState (model := PaymentMethod) (supply := supply)
    PaymentMethod.form (PaymentMethod.serverCheck { PaymentMethod.initial with
      value := some .blpCreditCard }) Env.nil
  check "PassingChecksAreResolved" (markers matching ==
    [[{ kind := warning .resolved false, text := "The payment method matches the receipt." },
      receipt]])
  let some control := opened.evaluation.view.controls.find? (·.label == label)
    | throw (IO.userError s!"Missing control: {label}")
  let cleared ← IO.ofExcept (ModelForm.execute (model := PaymentMethod) PaymentMethod.form opened
    (.apply control.key (some (.text "none"))))
  let outdated := [[{ kind := warning .unresolved true, text := mismatch },
    { receipt with kind := info .unresolved true }]]
  check "EditsOutdateServerChecks" (cleared.value.value == none && markers cleared == outdated)
  let pending ← IO.ofExcept (ModelForm.execute (model := PaymentMethod) PaymentMethod.form cleared
    .submit)
  check "ReportsDoNotBlockSubmit" (pending.outbox.contains .submit)
  let refused ← IO.ofExcept (ModelForm.execute (model := PaymentMethod) PaymentMethod.form pending
    (.submitted (.rejected rejected)))
  check "RejectedSubmitKeepsChecksOutdated" (markers refused == outdated)
  let saved ← IO.ofExcept (ModelForm.execute (model := PaymentMethod) PaymentMethod.form pending
    (.submitted (.accepted (PaymentMethod.serverCheck pending.value))))
  check "SavedDocumentReplacesChecks"
    (markers saved ==
        [[{ kind := warning .unresolved false, text := "Choose a payment method." }, receipt]] &&
      !saved.ui.pending)
  let reset ← IO.ofExcept
    (ModelForm.execute (model := PaymentMethod) PaymentMethod.form saved .reset)
  check "ResetReturnsToSavedDocument"
    (reset.value.value == none && markers reset == markers saved)

end Tests.Reports
