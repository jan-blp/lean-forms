module

public import Forms.Model.Sugar
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model Forms.Model.Sugar

structure FailingCheck where
  message : String
  isFailing : Bool
  isMandatory : Bool
  canBeResolvedWithApproving : Bool
  isResolvedWithApproving : Bool
  deriving BEq, DecidableEq, Repr, Lean.ToJson, Lean.FromJson

/-- Approving would resolve it, or already did. -/
def FailingCheck.approvable (check : FailingCheck) : Bool :=
  check.isResolvedWithApproving || check.isFailing && check.canBeResolvedWithApproving

inductive ExpensePaymentMethod where
  | blpCreditCard
  | privatelyPaid
  deriving FormModel

@[report_rule] structure PaymentMethod where
  value : Option ExpensePaymentMethod
  /-- The value the user approved; the approval holds while it equals `value`. -/
  approved : Option ExpensePaymentMethod
  checks : ReadOnly (List FailingCheck)
  disabled : ReadOnly Bool
  visible : ReadOnly Bool
  deriving FormModel

instance : ReportRule PaymentMethod where
  reports raw := raw.checks.value.filter (fun check => check.isMandatory || check.isFailing)
    |>.map fun check =>
    { status :=
        if check.isResolvedWithApproving then .resolved .approved
        else if check.isFailing then .unresolved
        else .resolved .passed
      severity := if check.isMandatory then .warning else .info
      message := check.message
      targets := .locations (.field PaymentMethod.Field.value .self) }

def PaymentMethod.field {Γ : Context} : Component Γ PaymentMethod.Raw :=
  .visibleWhen { inputs := inputs[path[PaymentMethod.Field.visible]], run := (·.value) } <|
  .disabledWhen { inputs := inputs[path[PaymentMethod.Field.disabled]], run := (·.value) } <|
  .optional path[PaymentMethod.Field.value] "Expense Payment Method" "Not set" "Set" .blpCreditCard
    (.enum .self "Method" [⟨.blpCreditCard, "BLP credit card"⟩, ⟨.privatelyPaid, "Privately paid"⟩])

def PaymentMethod.form : Component [] PaymentMethod.Raw := named%
  observe% currentIssues := .issues;
  let issues : Computation _ PaymentMethod.Raw (List Issue) := {
    inputs := inputs[.ui ref[currentIssues]], run := id }
  .group "Payment" [
    .statusMarkerAt path[PaymentMethod.Field.value],
    PaymentMethod.field,
    .visibleWhen {
        inputs := inputs[
          path[PaymentMethod.Field.value],
          path[PaymentMethod.Field.approved],
          path[PaymentMethod.Field.checks]]
        run := fun value approved checks =>
          value.isSome && approved != value && checks.value.any (·.approvable) } <|
      .button "Approve" (.write path[PaymentMethod.Field.approved]
        { inputs := inputs[path[PaymentMethod.Field.value]], run := id }),
    .visibleWhen {
        inputs := inputs[path[PaymentMethod.Field.value], path[PaymentMethod.Field.approved]]
        run := fun value approved => value.isSome && approved == value } <|
      .button "Withdraw approval" (.write path[PaymentMethod.Field.approved] (.const none)),
    .computed "Current issues" ((fun issues =>
      String.intercalate "\n" (issues.map (·.message))) <$> issues),
    .disabledWhen (List.isEmpty <$> issues) <|
      .button "Go to issue"
        (.visit ((fun issues => issues.head?.bind (·.destination?)) <$> issues))]

def PaymentMethod.receiptCheck : FailingCheck where
  message := "Attach the original receipt."
  isFailing := true
  isMandatory := false
  canBeResolvedWithApproving := false
  isResolvedWithApproving := false

def PaymentMethod.initial : PaymentMethod.Raw where
  value := some .privatelyPaid
  approved := none
  checks := ⟨[
    { message := "The payment method does not match the receipt."
      isFailing := true
      isMandatory := true
      canBeResolvedWithApproving := true
      isResolvedWithApproving := false },
    PaymentMethod.receiptCheck]⟩
  disabled := ⟨false⟩
  visible := ⟨true⟩

end Forms.ExampleForms
