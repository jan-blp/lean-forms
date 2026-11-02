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
    (.require (fun n => 5 ≤ n ∧ n ≤ 30)
      (.and (.natLe (.value 5) (.project .self)) (.natLe (.project .self) (.value 30)))
      (.value "Temperature must be between 5 and 30 C.") (.fields [.self]))

def thermostatType : RefinedDataType thermostat :=
  .refine (.record fun _ => temperatureType)
    (.require (fun value => value .away ≤ value .home)
      (.natLe (.project awayTemperature) (.project homeTemperature))
      (.value "Away temperature must not exceed home temperature.")
      (.fields [awayTemperature.locationExpr])
      (by intro value; grind [Expr.eval, Path.get, awayTemperature, homeTemperature]))

def initial : RefinedDataType.ValidatedValue thermostatType := ⟨(fun | .home => ⟨(22 : Nat), by decide⟩ | .away => ⟨(18 : Nat), by decide⟩), by decide⟩
def draft : ⟦thermostat⟧ := RefinedDataType.erase thermostatType initial

def form : Component thermostat :=
  (show Component.Builder thermostat thermostat from
    Component.Builder.group "Thermostat" fun
      | .home => Component.Builder.field "Home temperature (C)" .naturalInput
      | .away => Component.Builder.field "Away temperature (C)" .naturalInput) .self

end Forms.ExampleForms.Thermostat
