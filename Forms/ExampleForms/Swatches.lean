module

public import Forms.Model.Sugar
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms.Swatches
open Lean Forms.Model Forms.Model.Sugar

structure Theme where
  dark : Bool
  accent : String
  deriving FormModel

structure Swatch where
  id : String
  label : String
  color : String
  deriving ToJson

structure PickerInput where
  swatches : List Swatch
  selected : String
  deriving ToJson

structure PickerOutput where
  id : String
  deriving FromJson

def palette (dark : Bool) : List Swatch :=
  if dark then
    [{ id := "blue", label := "Blue", color := "#60a5fa" },
     { id := "green", label := "Green", color := "#4ade80" },
     { id := "purple", label := "Purple", color := "#c084fc" }]
  else
    [{ id := "blue", label := "Blue", color := "#1d4ed8" },
     { id := "green", label := "Green", color := "#15803d" },
     { id := "orange", label := "Orange", color := "#c2410c" },
     { id := "purple", label := "Purple", color := "#7e22ce" }]

def picker : HostWidget PickerInput PickerOutput String where
  name := "swatchPicker"
  accept input output :=
    if input.swatches.any (·.id == output.id) then .ok output.id
    else .error s!"\"{output.id}\" is not one of the offered colours."

def form : Component [] Theme.Raw :=
  .group "Theme" [
    .field path[Theme.Field.dark] "Dark background" .checkbox,
    .hostWidget picker path[Theme.Field.accent] "Accent"
      { inputs := inputs[path[Theme.Field.dark], path[Theme.Field.accent]]
        run := fun dark accent => { swatches := palette dark, selected := accent } },
    .computed "Chosen accent" { inputs := inputs[path[Theme.Field.accent]], run := id }]

def initial : Theme.Raw := { dark := false, accent := "blue" }

end Forms.ExampleForms.Swatches
