module

public import Forms.ExampleForms.Registry
public import Forms.ExampleForms.PaymentMethod.Server
public import Forms.Runtime.ServerForm

@[expose] public section
namespace Forms.ExampleForms
open Forms.Runtime

def stored : List (String × ServerForm) := [
  ("payment-method", { form := paymentMethod, store := PaymentMethod.serverCheck })]

def serverForms : List (String × ServerForm) :=
  forms.map fun (name, form) => (name, (stored.lookup name).getD (.plain form))

end Forms.ExampleForms
