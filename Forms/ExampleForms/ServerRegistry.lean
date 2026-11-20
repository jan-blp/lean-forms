module

public import Forms.ExampleForms.Registry
public import Forms.ExampleForms.PaymentMethod.Server
public import Forms.ExampleForms.Receipts.Server
public import Forms.Runtime.ServerForm

@[expose] public section
namespace Forms.ExampleForms
open Forms.Runtime

def stored : List (String × ServerForm) := [
  ("payment-method", {
    form := paymentMethod
    State := Unit
    init := pure ()
    store := fun () => pure ∘ PaymentMethod.serverCheck }),
  ("receipts", {
    form := receipts
    State := Receipts.ServerState
    init := Receipts.ServerState.init
    store := Receipts.serverCheck })]

def documents : List (String × Viewer.Document) := [
  ("evidence", InvoiceHeader.document)]

def serverForms : List (String × ServerForm) :=
  forms.map fun (name, form) => (name, (stored.lookup name).getD (.plain form))

end Forms.ExampleForms
