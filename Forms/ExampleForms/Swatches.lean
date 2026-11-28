module

public import Forms.Model.Sugar
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms.Swatches
open Lean Forms.Model Forms.Model.Sugar

def colours : List String := ["blue", "green", "orange", "purple"]

abbrev Accent := { id : String // id ∈ colours }

def accent (id : String) (known : id ∈ colours := by simp [colours]) : Accent := ⟨id, known⟩

@[reducible] instance : FormModel Accent where
  Raw := Accent
  erase := id

instance : Validation Accent where
  validate value := .ok ⟨value, rfl⟩

instance : Reports Accent where
  reports _ := []

instance : ToJson Accent where
  toJson accent := toJson accent.val

instance : FromJson Accent where
  fromJson? json := do
    let id : String ← fromJson? json
    if known : id ∈ colours then pure ⟨id, known⟩ else throw s!"Unknown colour \"{id}\"."

structure Theme where
  dark : Bool
  accent : Accent
  deriving FormModel

structure Swatch where
  id : Accent
  label : String
  color : String
  deriving ToJson

structure PickerInput where
  swatches : List Swatch
  selected : Accent
  deriving ToJson

structure PickerOutput where
  id : String
  deriving FromJson

def palette (dark : Bool) : List Swatch :=
  if dark then
    [{ id := accent "blue", label := "Blue", color := "#60a5fa" },
     { id := accent "green", label := "Green", color := "#4ade80" },
     { id := accent "purple", label := "Purple", color := "#c084fc" }]
  else
    [{ id := accent "blue", label := "Blue", color := "#1d4ed8" },
     { id := accent "green", label := "Green", color := "#15803d" },
     { id := accent "orange", label := "Orange", color := "#c2410c" },
     { id := accent "purple", label := "Purple", color := "#7e22ce" }]

def picker : HostWidget PickerInput PickerOutput Accent where
  name := "swatchPicker"
  accept input output :=
    match input.swatches.find? (·.id.val == output.id) with
    | some swatch => .ok swatch.id
    | none => .error s!"\"{output.id}\" is not one of the offered colours."

def form : Component [] Theme.Raw :=
  .group "Theme" [
    .field path[Theme.Field.dark] "Dark background" .checkbox,
    .hostWidget picker path[Theme.Field.accent] "Accent"
      { inputs := inputs[path[Theme.Field.dark], path[Theme.Field.accent]]
        run := fun dark accent => { swatches := palette dark, selected := accent } },
    .computed "Chosen accent" { inputs := inputs[path[Theme.Field.accent]], run := (·.val) }]

def initial : Theme.Raw := { dark := false, accent := accent "blue" }

end Forms.ExampleForms.Swatches
