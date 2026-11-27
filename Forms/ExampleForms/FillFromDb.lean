module

public import Forms.Model.Sugar
public import Forms.Model.Endpoints
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms.FillFromDb
open Lean Forms.Model Forms.Model.Sugar

structure Payee where
  partner : String
  iban : String
  deriving FormModel

structure AccountQuery where
  partner : String
  deriving ToJson, FromJson

structure Account where
  iban : String
  deriving ToJson, FromJson

endpoints AccountEndpoint where
  | account : AccountQuery → Account at "/api/account"

def form : Component [] Payee.Raw := named%
  state% failure := (none : Option String);
  .group "Payee" [
    .field path[Payee.Field.partner] "Partner" .text,
    .button "Fill from DB" <|
      .call AccountEndpoint.account
        { inputs := inputs[path[Payee.Field.partner]], run := fun partner => ({ partner } : AccountQuery) }
        fun result => match result with
          | .ok account =>
            .write path[Payee.Field.iban] (.const account.iban) * .set ref[failure] (.const none)
          | .error message => .set ref[failure] (.const (some message)),
    .visibleWhen { inputs := inputs[ref[failure]], run := Option.isSome }
      (.computed "Lookup failed" { inputs := inputs[ref[failure]], run := (·.getD "") }),
    .field path[Payee.Field.iban] "IBAN" .text]

def initial : Payee.Raw := ⟨"acme", ""⟩

def account : String → Option Account
  | "acme" => some { iban := "CH93 0076 2011 6238 5295 7" }
  | "globex" => some { iban := "DE89 3704 0044 0532 0130 00" }
  | _ => none

def answer : (named : AccountEndpoint) → named.signature.Input → Option named.signature.Output
  | .account, query => account query.partner

def serve : HttpRequest → Option Json :=
  Api.serve answer

end Forms.ExampleForms.FillFromDb
