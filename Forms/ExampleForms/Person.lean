module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms.Person
open Forms.Model

structure Address where
  street : String
  street_valid : street ≠ ""
  deriving FormModel

instance : ConstraintRule Address.Constraint.street_valid where
  check parts :=
    if h : parts.street ≠ "" then .valid h
    else .invalid h "Enter your delivery street." (.locations (.field Address.Field.street .self))

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
    else .invalid h "Enter your name." (.locations (.field Person.Field.name .self))

instance : ConstraintRule Person.Constraint.age_valid where
  check parts :=
    if h : parts.age ≤ 120 then .valid h
    else .invalid h "Age must be at most 120." (.locations (.field Person.Field.age .self))

instance : ConstraintRule Person.Constraint.campus_valid where
  check parts :=
    if h : parts.address.street = "Campus" → 18 ≤ parts.age then .valid h
    else .invalid h "Campus delivery requires an adult." (.locations (.field Person.Field.age .self))

def initial : Person.Raw := ⟨"Ada", 20, false, ⟨"Lambda Lane"⟩⟩

def form : Component Person.Raw := .group "Person" [
  .field (.field Person.Field.name .self) "Name" .text,
  .field (.field Person.Field.age .self) "Age" .natural,
  .field (.field Person.Field.delivery .self) "Request delivery" .checkbox,
  .computed "Summary" (.of (inputs[.field Person.Field.name .self, .field Person.Field.age .self])
    (fun name age => s!"{name}, age {age}")),
  .visibleWhen (.of (inputs[.field Person.Field.delivery .self]) id)
    (.group "Delivery" [
      .computed "Eligibility" (.of (inputs[.field Person.Field.age .self])
        (fun age => if age < 18 then "Delivery details require an adult." else "Ready for delivery.")),
      .disabledWhen (.of (inputs[.field Person.Field.age .self]) (fun age => decide (age < 18)))
        (.field (.field Person.Field.address (.field Address.Field.street .self)) "Street" .text)
    ])
]

end Forms.ExampleForms.Person
