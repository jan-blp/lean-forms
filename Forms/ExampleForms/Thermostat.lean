import Forms.Core.Form
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Thermostat

abbrev shape : DataType := .group (n := 2) (fun _ => .natural)

def homeTemperature : Path shape .natural := .child 0 .here
def awayTemperature : Path shape .natural := .child 1 .here

/-- Shared by both temperature fields; values are whole degrees Celsius. -/
def temperatureType : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .and (.natLe (.value 5) (.project .here))
        (.natLe (.project .here) (.value 30))
      errorMessage := "Temperature must be between 5 and 30 C."
      errorLocation := some ⟨.here⟩ }

def thermostatType : RefinedDataType shape :=
  .refine (.group fun _ => temperatureType)
    { condition := .natLe (.project awayTemperature) (.project homeTemperature)
      errorMessage := "Away temperature must not exceed home temperature."
      errorLocation := some ⟨awayTemperature⟩ }

def initial : thermostatType.denote := ⟨(![⟨22, by decide⟩, ⟨18, by decide⟩] : Fin 2 → temperatureType.denote), by decide⟩
def draft : DataType.denote shape := thermostatType.erase initial

def form : Form shape shape :=
  .group "Thermostat" fun
    | 0 => .field "Home temperature (C)" .naturalInput
    | 1 => .field "Away temperature (C)" .naturalInput

end Forms.ExampleForms.Thermostat
