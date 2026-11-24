module

public import Forms.Model.Component
public meta import Forms.Model.Derive
public meta import Forms.Deriving.FinEnum

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

inductive DeliveryEndpoint where
  | countries
  | cities
  deriving DecidableEq, FinEnum, Repr

def DeliveryEndpoint.signature : DeliveryEndpoint → Api.Signature
  | .countries => { Input := String, Output := LookupResults String }
  | .cities => { Input := CitySearch, Output := LookupResults String }

instance : Api DeliveryEndpoint where
  signature := DeliveryEndpoint.signature
  path
    | .countries => "/api/countries"
    | .cities => "/api/cities"
  distinct := by decide

def Delivery.form : Component [] Delivery.Raw :=
  .group "Delivery" [
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

/-- Case-insensitive. -/
def mentions (text : String) (record : Reference String) : Bool :=
  record.label.toLower.contains text.toLower

/-- A fake server that answers at most five matches. -/
def answer
  : (named : DeliveryEndpoint) → named.signature.Input → Option named.signature.Output
  | .countries, text => some (LookupResults.select countries (mentions text) 5)
  | .cities, (search : CitySearch) =>
    some (LookupResults.select (cities search.country) (mentions search.text) 5)

def serve : HttpRequest → Option Json :=
  Api.serve answer

end Delivery

end Forms.ExampleForms
