import Forms.Core.Form
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Thermostat

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

abbrev shape : DataType := .record temperatureFields (fun _ => .natural)

def homeTemperature : Path shape .natural := .child .home .self
def awayTemperature : Path shape .natural := .child .away .self

/-- Shared by both temperature fields; values are whole degrees Celsius. -/
def temperatureType : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .and (.natLe (.value 5) (.project .self))
        (.natLe (.project .self) (.value 30))
      errorMessage := "Temperature must be between 5 and 30 C."
      errorLocation := some ⟨.self⟩ }

def thermostatType : RefinedDataType shape :=
  .refine (.record fun _ => temperatureType)
    { condition := .natLe (.project awayTemperature) (.project homeTemperature)
      errorMessage := "Away temperature must not exceed home temperature."
      errorLocation := some ⟨awayTemperature⟩ }

def initial : RefinedDataType.ValidatedValue thermostatType := ⟨(fun | .home => ⟨(22 : Nat), by decide⟩ | .away => ⟨(18 : Nat), by decide⟩), by decide⟩
def draft : DataType.denote shape := RefinedDataType.erase thermostatType initial

def form : Form shape shape :=
  .group "Thermostat" fun
    | .home => .field "Home temperature (C)" .naturalInput
    | .away => .field "Away temperature (C)" .naturalInput

end Forms.ExampleForms.Thermostat
