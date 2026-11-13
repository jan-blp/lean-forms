module

public import Forms.ExampleForms.Person
public import Forms.ExampleForms.Order
public import Forms.ExampleForms.Expenses
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.Presentation.Wasm
open Forms.Model

structure Name where
  name : String
  deriving FormModel

def Name.form {Γ : Context} : Component Γ Name.Raw :=
  .field path[Name.Field.name] "Name" .text

def Name.initial : Name.Raw := ⟨"Ada"⟩

structure Address where
  street : String
  number : Nat
  street_valid : street ≠ ""
  number_valid : 1 ≤ number
  deriving FormModel

structure Thermostat where
  home : Nat
  away : Nat
  home_valid : 5 ≤ home ∧ home ≤ 30
  away_valid : 5 ≤ away ∧ away ≤ 30
  away_not_warmer : away ≤ home
  deriving FormModel

instance : ConstraintRule Thermostat.Constraint.home_valid where
  check parts :=
    if h : 5 ≤ parts.home ∧ parts.home ≤ 30 then .valid h
    else .invalid (proof := h) (message := "Temperature must be between 5 and 30 C.")
      (targets := locations[Thermostat.Field.home])

instance : ConstraintRule Thermostat.Constraint.away_valid where
  check parts :=
    if h : 5 ≤ parts.away ∧ parts.away ≤ 30 then .valid h
    else .invalid (proof := h) (message := "Temperature must be between 5 and 30 C.")
      (targets := locations[Thermostat.Field.away])

instance : ConstraintRule Thermostat.Constraint.away_not_warmer where
  check parts :=
    if h : parts.away ≤ parts.home then .valid h
    else .invalid (proof := h)
      (message := "Away temperature must not exceed home temperature.")
      (targets := locations[Thermostat.Field.away])

example : Fields.get Address.Field.number (⟨"Main", 7⟩ : Address.Raw) = 7 := rfl

end Forms.Presentation.Wasm

namespace Forms.ExampleForms
open Forms.Model


def pickupInfo {Γ : Context} : Component Γ Shipping.pickup.Raw := .computed "Pickup at" (.const "Store")
def standardAddress {Γ : Context} : Component Γ Shipping.standard.Raw :=
  .group "Address" (addressFields path[Shipping.standard.Field.address])
def courier {Γ : Context} : Component Γ Shipping.express.Raw :=
  .group "Courier" (addressFields path[Shipping.express.Field.address])

def shippingChoice {Γ : Context} : Component Γ Order.Raw :=
  .choice
    (path := path[Order.Field.shipping])
    (label := "Shipping")
    (branches := [
      .of Shipping.Constructor.pickup "Pickup" ⟨⟩ pickupInfo,
      .of Shipping.Constructor.standard "Standard" ⟨⟨"", ""⟩⟩ standardAddress,
      .of Shipping.Constructor.express "Express" ⟨⟨"", ""⟩, ""⟩ courier])

def selectedExpense : Component [] ExpenseReport.Raw :=
  .bind RowSelection.none (.group "Expense report" [
    .focus
      (target := {
        inputs := inputs[.ui .here]
        run := RowSelection.itemPath path[ExpenseReport.Field.expenses]
      })
      (body := .groupOf "Selected expense" Expense.columns.components)])

example (address : ShippingAddress.Raw)
  : Constructors.inject Shipping.Constructor.standard (⟨address⟩ : Shipping.standard.Raw)
    = Shipping.Raw.standard ⟨address⟩ := rfl

end Forms.ExampleForms
