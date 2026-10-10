import Forms.Core.Component.Builder
import Forms.Core.RefinedDataType

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
    { condition := .and (.natLe (.value 5) (.project .self))
        (.natLe (.project .self) (.value 30))
      errorMessage := "Temperature must be between 5 and 30 C."
      errorLocation := some ⟨.self⟩ }

def thermostatType : RefinedDataType thermostat :=
  .refine (.record fun _ => temperatureType)
    { condition := .natLe (.project awayTemperature) (.project homeTemperature)
      errorMessage := "Away temperature must not exceed home temperature."
      errorLocation := some ⟨awayTemperature⟩ }

def initial : RefinedDataType.ValidatedValue thermostatType := ⟨(fun | .home => ⟨(22 : Nat), by decide⟩ | .away => ⟨(18 : Nat), by decide⟩), by decide⟩
def draft : ⟦thermostat⟧ := RefinedDataType.erase thermostatType initial

def form : Component thermostat :=
  (show Component.Builder thermostat thermostat from
    Component.Builder.group "Thermostat" fun
      | .home => Component.Builder.field "Home temperature (C)" .naturalInput
      | .away => Component.Builder.field "Away temperature (C)" .naturalInput) .self

end Forms.ExampleForms.Thermostat
