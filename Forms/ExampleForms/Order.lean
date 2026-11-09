module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

/-! Rules are named: auto-generated names clash with Person's (e.g. `name_valid`). -/

structure Customer where
  name : String
  email : String
  name_valid : name ≠ ""
  email_valid : email.contains '@' = true
  deriving FormModel

instance Customer.name_valid_rule : ConstraintRule Customer.Constraint.name_valid where
  check parts :=
    if h : parts.name ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter the customer name.")
      (targets := locations[Customer.Field.name])

instance Customer.email_valid_rule : ConstraintRule Customer.Constraint.email_valid where
  check parts :=
    if h : parts.email.contains '@' = true then .valid h
    else .invalid (proof := h) (message := "Enter a valid email address.")
      (targets := locations[Customer.Field.email])

structure Shipping where
  street : String
  city : String
  express : Bool
  street_valid : street ≠ ""
  city_valid : city ≠ ""
  deriving FormModel

instance Shipping.street_valid_rule : ConstraintRule Shipping.Constraint.street_valid where
  check parts :=
    if h : parts.street ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter the shipping street.")
      (targets := locations[Shipping.Field.street])

instance Shipping.city_valid_rule : ConstraintRule Shipping.Constraint.city_valid where
  check parts :=
    if h : parts.city ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter the shipping city.")
      (targets := locations[Shipping.Field.city])

structure Order where
  customer : Customer
  quantity : Nat
  unitPrice : Nat
  gift : Bool
  giftMessage : String
  shipping : Shipping
  quantity_min : 1 ≤ quantity
  quantity_max : quantity ≤ 100
  gift_valid : gift = true → giftMessage ≠ ""
  express_valid : shipping.express = true → quantity ≤ 10
  deriving FormModel

instance Order.quantity_min_rule : ConstraintRule Order.Constraint.quantity_min where
  check parts :=
    if h : 1 ≤ parts.quantity then .valid h
    else .invalid (proof := h) (message := "Order at least one item.")
      (targets := locations[Order.Field.quantity])

instance Order.quantity_max_rule : ConstraintRule Order.Constraint.quantity_max where
  check parts :=
    if h : parts.quantity ≤ 100 then .valid h
    else .invalid (proof := h) (message := "Order at most 100 items.")
      (targets := locations[Order.Field.quantity])

instance Order.gift_valid_rule : ConstraintRule Order.Constraint.gift_valid where
  check parts :=
    if h : parts.gift = true → parts.giftMessage ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter a gift message.")
      (targets := locations[Order.Field.giftMessage])

instance Order.express_valid_rule : ConstraintRule Order.Constraint.express_valid where
  check parts :=
    if h : parts.shipping.express = true → parts.quantity ≤ 10 then .valid h
    else .invalid (proof := h) (message := "Express shipping is limited to 10 items.")
      (targets := locations[Order.Field.quantity])

/-- Swiss thousands separators, e.g. `12'345`. -/
def swiss (n : Nat) : String :=
  if n < 1000 then toString n
  else
    let rest := n % 1000
    let pad := if rest < 10 then "00" else if rest < 100 then "0" else ""
    swiss (n / 1000) ++ "'" ++ pad ++ toString rest
termination_by n
decreasing_by omega

def Order.initial : Order.Raw :=
  ⟨⟨"Grace Hopper", "grace@example.com"⟩, 2, 45, false, "", ⟨"Bahnhofstrasse 1", "Zürich", false⟩⟩

def Order.form : Component Order.Raw :=
  .group (label := "Order") (children := [
    .group (label := "Customer") (children := [
      .field
        (path := path[Order.Field.customer, Customer.Field.name])
        (label := "Customer name")
        (editor := .text),
      .field
        (path := path[Order.Field.customer, Customer.Field.email])
        (label := "Email")
        (editor := .text)]),
    .group (label := "Items") (children := [
      .field
        (path := path[Order.Field.quantity])
        (label := "Quantity")
        (editor := .natural),
      .field
        (path := path[Order.Field.unitPrice])
        (label := "Unit price (CHF)")
        (editor := .natural),
      .computed
        (label := "Total")
        (value := {
          inputs := inputs[path[Order.Field.quantity], path[Order.Field.unitPrice]]
          run := fun quantity price => s!"CHF {swiss (quantity * price)}"
        })]),
    .field
      (path := path[Order.Field.gift])
      (label := "Gift wrap")
      (editor := .checkbox),
    .visibleWhen
      (condition := {
        inputs := inputs[path[Order.Field.gift]]
        run := id
      })
      (body := .group (label := "Gift") (children := [
        .field
          (path := path[Order.Field.giftMessage])
          (label := "Gift message")
          (editor := .text),
        .visibleWhen
          (condition := {
            inputs := inputs[path[Order.Field.giftMessage]]
            run := fun message => message != ""
          })
          (body := .computed
            (label := "Card preview")
            (value := {
              inputs := inputs[path[Order.Field.giftMessage], path[Order.Field.customer, Customer.Field.name]]
              run := fun message name => s!"\"{message}\" from {name}"
            }))])),
    .group (label := "Shipping") (children := [
      .field
        (path := path[Order.Field.shipping, Shipping.Field.street])
        (label := "Street")
        (editor := .text),
      .field
        (path := path[Order.Field.shipping, Shipping.Field.city])
        (label := "City")
        (editor := .text),
      .disabledWhen
        (condition := {
          inputs := inputs[path[Order.Field.quantity]]
          run := fun quantity => decide (quantity > 10)
        })
        (body := .field
          (path := path[Order.Field.shipping, Shipping.Field.express])
          (label := "Express shipping")
          (editor := .checkbox)),
      .computed
        (label := "Delivery")
        (value := {
          inputs := inputs[path[Order.Field.shipping, Shipping.Field.express]]
          run := fun express => if express then "Next business day" else "3 to 5 business days"
        })])
  ])

end Forms.ExampleForms
