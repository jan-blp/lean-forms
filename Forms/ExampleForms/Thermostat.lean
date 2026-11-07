module

public import Forms.Core.Component.Builder
public import Forms.Core.RefinedDataType

@[expose] public section

namespace Forms.ExampleForms.Thermostat
open Composition

inductive TemperatureField where
  | home | away
  deriving DecidableEq, Repr

instance : FinEnum TemperatureField :=
  FinEnum.ofList [.home, .away] (by grind [TemperatureField])

def temperatureFields : Enum where
  type := TemperatureField
  label
    | .home => "home"
    | .away => "away"

abbrev thermostat : DataType := .record temperatureFields (fun _ => .natural)

def homeTemperature : Path thermostat .natural := .field .home .self
def awayTemperature : Path thermostat .natural := .field .away .self

/-- Shared by both temperature fields; values are whole degrees Celsius. -/
def temperatureType : RefinedDataType .natural :=
  .refine (.base .natural)
    (.require (fun n => 5 ≤ n ∧ n ≤ 30)
      (fun _ => "Temperature must be between 5 and 30 C.") (fun _ _ => .locations [.self]))

def thermostatType : RefinedDataType thermostat :=
  .refine (.record fun _ => temperatureType)
    (.require (fun value => value .away ≤ value .home)
      (fun _ => "Away temperature must not exceed home temperature.")
      (fun value _ => .locations [awayTemperature.validLocation value]))

def initial : RefinedDataType.ValidatedValue thermostatType := ⟨(fun | .home => ⟨(22 : Nat), by decide⟩ | .away => ⟨(18 : Nat), by decide⟩), by decide⟩
def draft : ⟦thermostat⟧ := RefinedDataType.erase thermostatType initial

def form : Component thermostat :=
  (show Component.Builder thermostat thermostat from
    Component.Builder.group "Thermostat" fun
      | .home => Component.Builder.field "Home temperature (C)" .naturalInput
      | .away => Component.Builder.field "Away temperature (C)" .naturalInput) .self

end Forms.ExampleForms.Thermostat
