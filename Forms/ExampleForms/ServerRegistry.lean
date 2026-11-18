module

public import Forms.ExampleForms.Registry
public import Forms.ExampleForms.PaymentMethod.Server
public import Forms.ExampleForms.Receipts.Server
public import Forms.Runtime.ServerForm

@[expose] public section
namespace Forms.ExampleForms
open Forms.Runtime

structure ServerState where
  claims : IO.Ref (Std.HashMap String Model.Uuid)

def ServerState.create : IO ServerState := do
  return { claims := ← IO.mkRef {} }

def serverForms (state : ServerState) : List (String × ServerForm) :=
  let stored : List (String × ServerForm) := [
    ("payment-method", {
      form := paymentMethod
      store := pure ∘ PaymentMethod.serverCheck }),
    ("receipts", {
      form := receipts
      store := Receipts.serverCheck state.claims })]
  forms.map fun (name, form) => (name, (stored.lookup name).getD (.plain form))

end Forms.ExampleForms
