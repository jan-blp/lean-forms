module

public import Forms.Model.Component
public import Forms.Model.Endpoints
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Lean Forms.Model

structure Delivery where
  country : Option (Reference String)
  city : Option (Reference String)
  deriving FormModel

structure CitySearch where
  country : String
  text : String
  deriving ToJson, FromJson

endpoints DeliveryEndpoint where
  | countries : String → LookupResults String at "/api/countries"
  | cities : CitySearch → LookupResults String at "/api/cities"

def Delivery.form : Component [] Delivery.Raw :=
  .group "Delivery" [
    .onChange (fun before after =>
      if before.country.map (·.id) == after.country.map (·.id) then after
      else { after with city := none }) <|
      .lookup path[Delivery.Field.country] "Country" (.const (Api.source DeliveryEndpoint.countries)),
    .disabledWhen { inputs := inputs[path[Delivery.Field.country]], run := Option.isNone } <|
      .lookup path[Delivery.Field.city] "City"
        { inputs := inputs[path[Delivery.Field.country]]
          run := fun country text => match country with
            | some country => Api.source DeliveryEndpoint.cities { country := country.id, text }
            | none => .pure .empty }]

def Delivery.initial : Delivery.Raw := ⟨none, none⟩

namespace Delivery

def countries : List (Reference String) := [
  ⟨"AT", "Austria"⟩,
  ⟨"BE", "Belgium"⟩,
  ⟨"DE", "Germany"⟩,
  ⟨"ES", "Spain"⟩,
  ⟨"FR", "France"⟩,
  ⟨"IT", "Italy"⟩,
  ⟨"NL", "Netherlands"⟩,
  ⟨"PT", "Portugal"⟩]

def cities : String → List (Reference String)
  | "DE" => [⟨"BER", "Berlin"⟩, ⟨"HAM", "Hamburg"⟩, ⟨"MUC", "Munich"⟩]
  | "ES" => [⟨"BCN", "Barcelona"⟩, ⟨"MAD", "Madrid"⟩, ⟨"VLC", "Valencia"⟩]
  | "FR" => [⟨"LYS", "Lyon"⟩, ⟨"MRS", "Marseille"⟩, ⟨"PAR", "Paris"⟩]
  | _ => []

def mentions (text : String) (record : Reference String) : Bool :=
  record.displayText.toLower.contains text.toLower

def answer
  : (named : DeliveryEndpoint) → named.signature.Input → Option named.signature.Output
  | .countries, text => (LookupResults.select countries (mentions text) 5).toOption
  | .cities, (search : CitySearch) =>
    (LookupResults.select (cities search.country) (mentions search.text) 5).toOption

def serve : HttpRequest → Option Json :=
  Api.serve answer

end Delivery

end Forms.ExampleForms
