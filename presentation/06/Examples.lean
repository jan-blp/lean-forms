module

public import Forms.Model.Sugar
public import Forms.Model.Endpoints
public meta import Forms.Model.Derive
public meta import Forms.Deriving.FinEnum

@[expose] public section
namespace Forms.Presentation.Loading
open Lean Forms.Model Forms.Model.Sugar

inductive Currency where
  | eur
  | usd
  | chf
  deriving FormModel

structure Invoice where
  amount : Nat
  currency : Currency
  deriving FormModel

namespace ByHand

inductive RatesEndpoint where
  | currencies
  | rate
  deriving DecidableEq, FinEnum

instance : Api RatesEndpoint where
  signature
    | .currencies => { Input := Unit, Output := List Currency.Raw }
    | .rate => { Input := Currency.Raw, Output := Nat }
  path
    | .currencies => "/api/currencies"
    | .rate => "/api/rate"
  distinct := by decide

example : Source (List Currency.Raw) := Api.source RatesEndpoint.currencies ()

end ByHand

endpoints RatesEndpoint where
  | currencies : List Currency.Raw at "/api/currencies"
  | rate : Currency.Raw → Nat at "/api/rate"

def Invoice.form : Component [] Invoice.Raw :=
  .group "Invoice" [
    .enum path[Invoice.Field.currency] "Currency"
      [⟨.eur, "EUR"⟩, ⟨.usd, "USD"⟩, ⟨.chf, "CHF"⟩],
    .loadWith (data := Nat)
      (compute%
        (currency : Currency.Raw) ← path[Invoice.Field.currency]
        => Api.source RatesEndpoint.rate currency)
      (fun value =>
        .computed "Rate" (.const (toString value)))]

example : Source (List Currency.Raw) := Api.source RatesEndpoint.currencies ()

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

def Delivery.cityLookup : Component [] Delivery.Raw :=
  .lookup path[Delivery.Field.city] "City"
    (compute%
      (country : Option (Reference String)) ← path[Delivery.Field.country]
      => fun text => match country with
        | some country => Api.source DeliveryEndpoint.cities { country := country.id, text }
        | none => .pure .empty)
    (.const LookupAvailability.always)

def Delivery.form : Component [] Delivery.Raw :=
  .group "Delivery" [
    .lookup path[Delivery.Field.country] "Country"
      (.const (Api.source DeliveryEndpoint.countries))
      (.const LookupAvailability.always),
    Delivery.cityLookup]

end Forms.Presentation.Loading
