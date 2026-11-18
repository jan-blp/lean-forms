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
  reports raw := raw.checks.value.filter (·.isFailing) |>.map fun check =>
    { message := check.message
      targets := .locations (.field PaymentMethod.Field.value .self) }

def PaymentMethod.form : Component [] PaymentMethod.Raw :=
  .visibleWhen { inputs := inputs[path[PaymentMethod.Field.visible]], run := (·.value) } <|
  .disabledWhen { inputs := inputs[path[PaymentMethod.Field.disabled]], run := (·.value) } <|
  .optional path[PaymentMethod.Field.value] "Expense Payment Method" "Not set" "Set" .blpCreditCard
    (.enum .self "Method" [⟨.blpCreditCard, "BLP credit card"⟩, ⟨.privatelyPaid, "Privately paid"⟩])

def PaymentMethod.serverCheck (raw : PaymentMethod.Raw) : PaymentMethod.Raw :=
  let check := match raw.value with
    | none =>
      { message := "Choose a payment method."
        isFailing := true
        isMandatory := true
        canBeResolvedWithApproving := false }
    | some .privatelyPaid =>
      { message := "The payment method does not match the receipt."
        isFailing := true
        isMandatory := true
        canBeResolvedWithApproving := true }
    | some .blpCreditCard =>
      { message := "The payment method matches the receipt."
        isFailing := false
        isMandatory := true
        canBeResolvedWithApproving := false }
  { raw with checks := ⟨[check]⟩ }

def PaymentMethod.initial : PaymentMethod.Raw where
  value := some .privatelyPaid
  checks := ⟨[
    { message := "The payment method does not match the receipt."
      isFailing := true
      isMandatory := true
      canBeResolvedWithApproving := true },
    { message := "This check passed and is not shown."
      isFailing := false
      isMandatory := false
      canBeResolvedWithApproving := false }]⟩
  disabled := ⟨false⟩
  visible := ⟨true⟩

end Forms.ExampleForms
