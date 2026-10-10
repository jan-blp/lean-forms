import Forms.Core.Component.Builder
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Location
open Composition

inductive Country where
  | france | japan | catalonia
  deriving DecidableEq, Repr

instance : FinEnum Country :=
  FinEnum.ofList [.france, .japan, .catalonia] (by grind [Country])

def countries : Enum where
  type := Country
  label
    | .france => "France"
    | .japan => "Japan"
    | .catalonia => "Catalonia"

inductive FrenchCity where
  | paris | lyon | marseille
  deriving DecidableEq, Repr

instance : FinEnum FrenchCity :=
  FinEnum.ofList [.paris, .lyon, .marseille] (by grind [FrenchCity])

def frenchCities : Enum where
  type := FrenchCity
  label
    | .paris => "Paris"
    | .lyon => "Lyon"
    | .marseille => "Marseille"

inductive JapaneseCity where
  | tokyo | kyoto | osaka
  deriving DecidableEq, Repr

instance : FinEnum JapaneseCity :=
  FinEnum.ofList [.tokyo, .kyoto, .osaka] (by grind [JapaneseCity])

def japaneseCities : Enum where
  type := JapaneseCity
  label
    | .tokyo => "Tokyo"
    | .kyoto => "Kyoto"
    | .osaka => "Osaka"

inductive CatalanCity where
  | vic | barcelona | girona
  deriving DecidableEq, Repr

instance : FinEnum CatalanCity :=
  FinEnum.ofList [.vic, .barcelona, .girona] (by grind [CatalanCity])

def catalanCities : Enum where
  type := CatalanCity
  label
    | .vic => "Vic"
    | .barcelona => "Barcelona"
    | .girona => "Girona"

abbrev constructors : countries → DataType
  | .france => .enum frenchCities
  | .japan => .enum japaneseCities
  | .catalonia => .enum catalanCities

abbrev location : DataType := .sum countries constructors

def locationType : RefinedDataType location := .sum (fun _ => .base _)

def initial : RefinedDataType.ValidatedValue locationType := ⟨.france, .paris⟩
def draft : ⟦location⟧ := RefinedDataType.erase locationType initial

def form : Component location :=
  (show Component.Builder location location from
    Component.Builder.sum "Country"
      (fun
        | .france => Component.Builder.field "City" .select
        | .japan => Component.Builder.field "City" .select
        | .catalonia => Component.Builder.field "City" .select)
      (fun
        | .france => .paris
        | .japan => .tokyo
        | .catalonia => .vic)) .self

end Forms.ExampleForms.Location
