import Forms.Core.Form
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Location

inductive Country where
  | france | japan
  deriving DecidableEq, Repr

instance : FinEnum Country :=
  FinEnum.ofList [.france, .japan] (by grind [Country])

def countries : Enum where
  type := Country
  label
    | .france => "France"
    | .japan => "Japan"

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

abbrev constructors : countries → DataType
  | .france => .enum frenchCities
  | .japan => .enum japaneseCities

abbrev location : DataType := .sum countries constructors

def locationType : RefinedDataType location := .sum (fun _ => .base _)

def initial : RefinedDataType.ValidatedValue locationType := ⟨.france, .paris⟩
def draft : DataType.denote location := RefinedDataType.erase locationType initial

def form : Form location location :=
  .sum "Country"
    (fun
      | .france => .field "City" .select
      | .japan => .field "City" .select)
    (fun
      | .france => .paris
      | .japan => .tokyo)

end Forms.ExampleForms.Location
