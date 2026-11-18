module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

structure FailingCheck where
  message : String
  isFailing : Bool
  isMandatory : Bool
  canBeResolvedWithApproving : Bool
  deriving BEq, DecidableEq, Repr, Lean.ToJson, Lean.FromJson

inductive ExpensePaymentMethod where
  | blpCreditCard
  | privatelyPaid
  deriving FormModel

@[report_rule] structure PaymentMethod where
  value : Option ExpensePaymentMethod
  checks : ReadOnly (List FailingCheck)
  disabled : ReadOnly Bool
  visible : ReadOnly Bool
  deriving FormModel

instance : ReportRule PaymentMethod where
  reports raw := raw.checks.value.filter (fun check => check.isMandatory || check.isFailing)
    |>.map fun check =>
    { status := if check.isFailing then .unresolved else .resolved
      severity := if check.isMandatory then .warning else .info
      message := check.message
      targets := .locations (.field PaymentMethod.Field.value .self) }

def PaymentMethod.field {Γ : Context} : Component Γ PaymentMethod.Raw :=
  .visibleWhen { inputs := inputs[path[PaymentMethod.Field.visible]], run := (·.value) } <|
  .disabledWhen { inputs := inputs[path[PaymentMethod.Field.disabled]], run := (·.value) } <|
  .optional path[PaymentMethod.Field.value] "Expense Payment Method" "Not set" "Set" .blpCreditCard
    (.enum .self "Method" [⟨.blpCreditCard, "BLP credit card"⟩, ⟨.privatelyPaid, "Privately paid"⟩])

def PaymentMethod.form : Component [] PaymentMethod.Raw :=
  .observe .issues <|
    let issues : Computation _ PaymentMethod.Raw (List Issue) := {
      inputs := inputs[.ui (Ref.here : InputRef _ (List Issue))]
      run := id }
    .group "Payment" [
      .statusMarkerAt path[PaymentMethod.Field.value],
      PaymentMethod.field,
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

def PaymentMethod.initial : PaymentMethod.Raw where
  value := some .privatelyPaid
  checks := ⟨[
    { message := "The payment method does not match the receipt."
      isFailing := true
      isMandatory := true
      canBeResolvedWithApproving := true },
    PaymentMethod.receiptCheck]⟩
  disabled := ⟨false⟩
  visible := ⟨true⟩

end Forms.ExampleForms
