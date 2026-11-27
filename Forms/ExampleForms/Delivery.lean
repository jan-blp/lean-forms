module

public import Forms.Model.Component
public import Forms.Model.SearchSelect
public import Forms.Model.Endpoints
public meta import Forms.Model.Derive
public meta import Forms.Deriving.FinEnum

@[expose] public section
namespace Forms.ExampleForms
open Lean Forms.Model

inductive Country where
  | austria
  | belgium
  | germany
  | catalonia
  | france
  | italy
  | netherlands
  | portugal
  | switzerland
  deriving DecidableEq, Repr, FinEnum, ToJson, FromJson

def Country.name : Country → String
  | .austria => "Austria"
  | .belgium => "Belgium"
  | .germany => "Germany"
  | .catalonia => "Catalonia"
  | .france => "France"
  | .italy => "Italy"
  | .netherlands => "Netherlands"
  | .portugal => "Portugal"
  | .switzerland => "Switzerland"

def Country.cities : Country → List (Reference String)
  | .austria => [⟨"VIE", "Vienna"⟩, ⟨"GRZ", "Graz"⟩, ⟨"SZG", "Salzburg"⟩]
  | .belgium => [⟨"BRU", "Brussels"⟩, ⟨"ANR", "Antwerp"⟩, ⟨"GNE", "Ghent"⟩]
  | .germany => [⟨"BER", "Berlin"⟩, ⟨"HAM", "Hamburg"⟩, ⟨"MUC", "Munich"⟩]
  | .catalonia => [
    ⟨"VIC", "Vic"⟩,
    ⟨"GIR", "Girona"⟩,
    ⟨"BCN", "Barcelona"⟩,
    ⟨"TGN", "Tarragona"⟩,
    ⟨"LLE", "Lleida"⟩,
    ⟨"MAN", "Manresa"⟩]
  | .france => [⟨"LYS", "Lyon"⟩, ⟨"MRS", "Marseille"⟩, ⟨"PAR", "Paris"⟩]
  | .italy => [⟨"ROM", "Rome"⟩, ⟨"MIL", "Milan"⟩, ⟨"TRN", "Turin"⟩]
  | .netherlands => [⟨"AMS", "Amsterdam"⟩, ⟨"RTM", "Rotterdam"⟩, ⟨"UTC", "Utrecht"⟩]
  | .portugal => [⟨"LIS", "Lisbon"⟩, ⟨"OPO", "Porto"⟩, ⟨"BGZ", "Braga"⟩]
  | .switzerland => [⟨"ZRH", "Zürich"⟩, ⟨"GVA", "Geneva"⟩, ⟨"BRN", "Bern"⟩]

structure Delivery where
  country : Option (Reference Country)
  city : Option (Reference String)
  deriving FormModel

structure CitySearch where
  country : Country
  text : String
  deriving ToJson, FromJson

endpoints DeliveryEndpoint where
  | countries : String → LookupResults Country Unit at "/api/countries"
  | cities : CitySearch → LookupResults String Unit at "/api/cities"

def Delivery.form : Component [] Delivery.Raw :=
  .group "Delivery" [
    .onChange (fun before after =>
      if before.country.map (·.id) == after.country.map (·.id) then after
      else { after with city := none }) <|
      .group "Country" [
        .lookup path[Delivery.Field.country] "Country"
          (.const (Api.source DeliveryEndpoint.countries)) (.const OptionAvailability.always),
        .searchSelect path[Delivery.Field.country] "Country (composed)" "Search countries"
          (.const (Api.source DeliveryEndpoint.countries)) (.const OptionAvailability.always)],
    .disabledWhen { inputs := inputs[path[Delivery.Field.country]], run := Option.isNone } <|
      .lookup path[Delivery.Field.city] "City"
        { inputs := inputs[path[Delivery.Field.country]]
          run := fun country text => match country with
            | some country => Api.source DeliveryEndpoint.cities { country := country.id, text }
            | none => .pure .empty }
        (.const OptionAvailability.always)]

def Delivery.initial : Delivery.Raw := ⟨none, none⟩

namespace Delivery

def countries : List (Reference Country) :=
  (FinEnum.toList Country).map fun country => { id := country, displayText := country.name }

def mentions {Key : Type} (text : String) (record : LookupCandidate Key Unit) : Prop :=
  record.reference.displayText.toLower.contains text.toLower = true

instance {Key : Type} (text : String) : DecidablePred (mentions (Key := Key) text) :=
  fun record => inferInstanceAs (Decidable (record.reference.displayText.toLower.contains text.toLower = true))

def answer
  : (named : DeliveryEndpoint) → named.signature.Input → Option named.signature.Output
  | .countries, (text : String) =>
    (LookupResults.select (countries.map LookupCandidate.ofReference) (mentions text) 5).toOption
  | .cities, (search : CitySearch) =>
    (LookupResults.select (search.country.cities.map LookupCandidate.ofReference) (mentions search.text) 5).toOption

def serve : HttpRequest → Option Json :=
  Api.serve answer

end Delivery

end Forms.ExampleForms
