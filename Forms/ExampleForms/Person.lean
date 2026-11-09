module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

structure Address where
  street : String
  street_valid : street ≠ ""
  deriving FormModel

instance : ConstraintRule Address.Constraint.street_valid where
  check parts :=
    if h : parts.street ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter your delivery street.")
      (targets := locations[Address.Field.street])

structure Person where
  name : String
  age : Nat
  delivery : Bool
  address : Address
  name_valid : name ≠ ""
  age_valid : age ≤ 120
  campus_valid : address.street = "Campus" → 18 ≤ age
  deriving FormModel

instance : ConstraintRule Person.Constraint.name_valid where
  check parts :=
    if h : parts.name ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter your name.")
      (targets := locations[Person.Field.name])

instance : ConstraintRule Person.Constraint.age_valid where
  check parts :=
    if h : parts.age ≤ 120 then .valid h
    else .invalid (proof := h) (message := "Age must be at most 120.")
      (targets := locations[Person.Field.age])

instance : ConstraintRule Person.Constraint.campus_valid where
  check parts :=
    if h : parts.address.street = "Campus" → 18 ≤ parts.age then .valid h
    else .invalid (proof := h) (message := "Campus delivery requires an adult.")
      (targets := locations[Person.Field.age])

def Person.initial : Person.Raw := ⟨"Ada", 20, false, ⟨"Lambda Lane"⟩⟩

def Person.form : Component Person.Raw :=
  .group (label := "Person") (children := [
    .field
      (path := path[Person.Field.name])
      (label := "Name")
      (editor := .text),
    .field
      (path := path[Person.Field.name])
      (label := "Name Dup")
      (editor := .text),
    .field
      (path := path[Person.Field.age])
      (label := "Age")
      (editor := .natural),
    .field
      (path := path[Person.Field.delivery])
      (label := "Request delivery")
      (editor := .checkbox),
    .computed
      (label := "Summary")
      (value := {
        inputs := inputs[
          path[Person.Field.name],
          path[Person.Field.age]]
        run := fun name age => s!"{name}, age {age}"
      }),
    .visibleWhen
      (condition := {
        inputs := inputs[path[Person.Field.delivery]]
        run := id
      })
      (body := .group (label := "Delivery") (children := [
        .computed
          (label := "Eligibility")
          (value := {
            inputs := inputs[path[Person.Field.age]]
            run := fun age =>
              if age < 18 then "Delivery details require an adult." else "Ready for delivery."
          }),
        .disabledWhen
          (condition := {
            inputs := inputs[path[Person.Field.age]]
            run := fun age => decide (age < 18)
          })
          (body := .field
            (path := path[Person.Field.address, Address.Field.street])
            (label := "Street")
            (editor := .text))
      ]))
  ])

end Forms.ExampleForms
