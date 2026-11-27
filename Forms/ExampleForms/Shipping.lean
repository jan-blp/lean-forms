module

public import Forms.Model.Sugar
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms.Shipping
open Forms.Model

inductive Speed where
  | economy
  | standard
  | express
  deriving FormModel

structure Parcel where
  grams : Nat
  speed : Speed
  deriving FormModel

def expressLimit : Nat := 30000

def availability (grams : Nat) : Speed.Raw → OptionAvailability
  | .economy => .enabled
  | .standard => .enabled
  | .express =>
    if grams ≤ expressLimit then .enabled else .disabled "Express takes parcels up to 30 kg."

def form : Component [] Parcel.Raw :=
  .group "Parcel" [
    .field path[Parcel.Field.grams] "Weight (g)" .natural,
    .enumWithAvailability path[Parcel.Field.speed] "Speed"
      [⟨.economy, "Economy"⟩, ⟨.standard, "Standard"⟩, ⟨.express, "Express"⟩]
      { inputs := inputs[path[Parcel.Field.grams]], run := availability }]

def initial : Parcel.Raw := ⟨1250, .standard⟩

end Forms.ExampleForms.Shipping
