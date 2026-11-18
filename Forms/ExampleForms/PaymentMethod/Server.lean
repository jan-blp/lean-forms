module

public import Forms.ExampleForms.PaymentMethod

@[expose] public section
namespace Forms.ExampleForms

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
  { raw with checks := ⟨[check, PaymentMethod.receiptCheck]⟩ }

end Forms.ExampleForms
