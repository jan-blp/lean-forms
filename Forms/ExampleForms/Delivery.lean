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
  | countries : String → LookupResults String Unit at "/api/countries"
  | cities : CitySearch → LookupResults String Unit at "/api/cities"

def Delivery.form : Component [] Delivery.Raw :=
  .group "Delivery" [
    .onChange (fun before after =>
      if before.country.map (·.id) == after.country.map (·.id) then after
      else { after with city := none }) <|
      .lookup path[Delivery.Field.country] "Country" (.const (Api.source DeliveryEndpoint.countries))
        (.const LookupAvailability.always),
    .disabledWhen { inputs := inputs[path[Delivery.Field.country]], run := Option.isNone } <|
      .lookup path[Delivery.Field.city] "City"
        { inputs := inputs[path[Delivery.Field.country]]
          run := fun country text => match country with
            | some country => Api.source DeliveryEndpoint.cities { country := country.id, text }
            | none => .pure .empty }
        (.const LookupAvailability.always)]

def Delivery.initial : Delivery.Raw := ⟨none, none⟩

namespace Delivery

def countries : List (Reference String) := [
  ⟨"AT", "Austria"⟩,
  ⟨"BE", "Belgium"⟩,
  ⟨"DE", "Germany"⟩,
  ⟨"CAT", "Catalonia"⟩,
  ⟨"FR", "France"⟩,
  ⟨"IT", "Italy"⟩,
  ⟨"NL", "Netherlands"⟩,
  ⟨"PT", "Portugal"⟩]

def cities : String → List (Reference String)
  | "DE" => [⟨"BER", "Berlin"⟩, ⟨"HAM", "Hamburg"⟩, ⟨"MUC", "Munich"⟩]
  | "CAT" => [
    ⟨"VIC", "Vic"⟩,
    ⟨"GIR", "Girona"⟩,
    ⟨"BCN", "Barcelona"⟩,
    ⟨"TGN", "Tarragona"⟩,
    ⟨"LLE", "Lleida"⟩,
    ⟨"MAN", "Manresa"⟩]
  | "FR" => [⟨"LYS", "Lyon"⟩, ⟨"MRS", "Marseille"⟩, ⟨"PAR", "Paris"⟩]
  | _ => []

def mentions (text : String) (record : LookupCandidate String Unit) : Prop :=
  record.reference.displayText.toLower.contains text.toLower = true

instance (text : String) : DecidablePred (mentions text) :=
  fun record => inferInstanceAs (Decidable (record.reference.displayText.toLower.contains text.toLower = true))

def answer
  : (named : DeliveryEndpoint) → named.signature.Input → Option named.signature.Output
  | .countries, (text : String) =>
    (LookupResults.select (countries.map LookupCandidate.ofReference) (mentions text) 5).toOption
  | .cities, (search : CitySearch) =>
    (LookupResults.select ((cities search.country).map LookupCandidate.ofReference) (mentions search.text) 5).toOption

def serve : HttpRequest → Option Json :=
  Api.serve answer

end Delivery

end Forms.ExampleForms
