module

public import Forms.Model.Sugar
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms.PrivateState
open Forms.Model Forms.Model.Sugar

inductive Speed where
  | standard
  | express
  deriving FormModel

structure Shipment where
  recipient : String
  grams : Nat
  speed : Speed
  instructions : String
  insured : Bool
  deriving FormModel

inductive WeightUnit where
  | grams
  | kilograms
  deriving FormModel

def WeightUnit.show (grams : Nat) : WeightUnit.Raw → String
  | .grams => s!"{grams} g"
  | .kilograms =>
    let rest := toString (grams % 1000)
    s!"{grams / 1000}.{"".pushn '0' (3 - rest.length)}{rest} kg"

def form : Component [] Shipment.Raw := named%
  state% advanced := false;
  state% unit := WeightUnit.Raw.grams;
  .group "Shipment" [
    .field path[Shipment.Field.recipient] "Recipient" .text,
    .field path[Shipment.Field.grams] "Weight (g)" .natural,
    .stateSelect ref[unit] "Show weight in"
      (.const (.ofValues [⟨.grams, "Grams"⟩, ⟨.kilograms, "Kilograms"⟩] (by decide) (by decide)))
      Constructors.tag,
    .computed "Weight" {
      inputs := inputs[path[Shipment.Field.grams], ref[unit]], run := WeightUnit.show },
    .enum path[Shipment.Field.speed] "Speed" [⟨.standard, "Standard"⟩, ⟨.express, "Express"⟩],
    .stateField ref[advanced] "Show advanced options" .checkbox,
    .visibleWhen { inputs := inputs[ref[advanced]], run := id }
      (.group "Advanced" [
        .field path[Shipment.Field.instructions] "Delivery instructions" .text,
        .field path[Shipment.Field.insured] "Insured" .checkbox])]

def initial : Shipment.Raw := ⟨"Ada", 1250, .standard, "", false⟩

end Forms.ExampleForms.PrivateState
