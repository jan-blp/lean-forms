module

public import Forms.Model.Sugar
public import Forms.Model.Endpoints
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms.ExchangeRate
open Lean Forms.Model Forms.Model.Sugar

inductive Currency where
  | eur
  | usd
  | chf
  deriving FormModel

structure Transfer where
  amount : Decimal
  currency : Currency
  rate : Decimal
  deriving FormModel

structure Quote where
  currency : Currency.Raw
  rate : Decimal
  deriving DecidableEq, ToJson, FromJson

endpoints RateEndpoint where
  | rates : List Quote at "/api/rates"

def form : Component [] Transfer.Raw := named%
  observe% rates := .loadStatus (data := List Quote) (.const (Api.source RateEndpoint.rates ()));
  .group "Transfer" [
    .field path[Transfer.Field.amount] "Amount" .decimal,
    .onChange (fun before after =>
      if before.currency == after.currency then 1
      else .write path[Transfer.Field.rate] {
        inputs := inputs[ref[rates], path[Transfer.Field.currency], path[Transfer.Field.rate]]
        run := fun rates currency current => match rates with
          | .ready quotes => ((quotes.find? (·.currency == currency)).map (·.rate)).getD current
          | .loading
          | .failed _ => current }) <|
      .enum path[Transfer.Field.currency] "Currency"
        [⟨.eur, "EUR"⟩, ⟨.usd, "USD"⟩, ⟨.chf, "CHF"⟩],
    .field path[Transfer.Field.rate] "Rate to EUR" .decimal]

def initial : Transfer.Raw := ⟨⟨100, 0, by decide⟩, .eur, ⟨1, 0, by decide⟩⟩

def quotes : List Quote := [
  { currency := .eur, rate := ⟨1, 0, by decide⟩ },
  { currency := .usd, rate := ⟨92, 2, by decide⟩ },
  { currency := .chf, rate := ⟨107, 2, by decide⟩ }]

def answer : (named : RateEndpoint) → named.signature.Input → Option named.signature.Output
  | .rates, () => some quotes

def serve : HttpRequest → Option Json :=
  Api.serve answer

end Forms.ExampleForms.ExchangeRate
