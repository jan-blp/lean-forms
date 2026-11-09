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

structure ShippingAddress where
  street : String
  city : String
  street_valid : street ≠ ""
  city_valid : city ≠ ""
  deriving FormModel

instance ShippingAddress.street_valid_rule
  : ConstraintRule ShippingAddress.Constraint.street_valid where
  check parts :=
    if h : parts.street ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter the shipping street.")
      (targets := locations[ShippingAddress.Field.street])

instance ShippingAddress.city_valid_rule
  : ConstraintRule ShippingAddress.Constraint.city_valid where
  check parts :=
    if h : parts.city ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter the shipping city.")
      (targets := locations[ShippingAddress.Field.city])

inductive Shipping where
  | pickup
  | standard (address : ShippingAddress)
  | express (address : ShippingAddress) (phone : String) (phone_valid : phone ≠ "")
  deriving FormModel

instance Shipping.express_phone_valid_rule
  : ConstraintRule Shipping.Constraint.express_phone_valid where
  check parts :=
    if h : parts.phone ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter a phone number for the courier.")
      (targets := locations[Shipping.express.Field.phone])

def Shipping.isExpress : Shipping → Bool
  | .express .. => true
  | _ => false

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
  express_valid : shipping.isExpress = true → quantity ≤ 10
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
    if h : parts.shipping.isExpress = true → parts.quantity ≤ 10 then .valid h
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
  ⟨⟨"Grace Hopper", "grace@example.com"⟩, 2, 45, false, "", .standard ⟨⟨"Bahnhofstrasse 1", "Zürich"⟩⟩⟩

/-- Street and city of the address at `path`. -/
def addressFields {raw : Type} (path : Path raw ShippingAddress.Raw) : List (Component raw) := [
  .field
    (path := path.trans path[ShippingAddress.Field.street])
    (label := "Street")
    (editor := .text),
  .field
    (path := path.trans path[ShippingAddress.Field.city])
    (label := "City")
    (editor := .text)]

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
    .disabledWhen
      (condition := {
        inputs := inputs[path[Order.Field.quantity]]
        run := fun quantity => decide (quantity > 10)
      })
      (body := .field
        (path := path[Order.Field.gift])
        (label := "Gift wrap")
        (editor := .checkbox)),
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
    .choice
      (path := path[Order.Field.shipping])
      (label := "Shipping")
      (branches := [
        .of
          (constructor := Shipping.Constructor.pickup)
          (label := "Pickup")
          (initial := ⟨⟩)
          (body := .computed
            (label := "Pickup at")
            (value := { inputs := inputs[], run := "Store, Bahnhofstrasse 1, Zürich" })),
        .of
          (constructor := Shipping.Constructor.standard)
          (label := "Standard")
          (initial := ⟨⟨"", ""⟩⟩)
          (body := .group
            (label := "Address")
            (children := addressFields path[Shipping.standard.Field.address])),
        .of
          (constructor := Shipping.Constructor.express)
          (label := "Express")
          (initial := ⟨⟨"", ""⟩, ""⟩)
          (body := .group
            (label := "Courier")
            (children := addressFields path[Shipping.express.Field.address] ++ [
              .field
                (path := path[Shipping.express.Field.phone])
                (label := "Phone")
                (editor := .text)]))]),
    .computed
      (label := "Delivery")
      (value := {
        inputs := inputs[path[Order.Field.shipping]]
        run := fun
          | .pickup => "Ready tomorrow"
          | .standard _ => "3 to 5 business days"
          | .express _ => "Next business day"
      })
  ])

end Forms.ExampleForms
