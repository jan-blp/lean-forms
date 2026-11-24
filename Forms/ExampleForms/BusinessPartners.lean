module

public import Forms.Model.Component
public import Forms.Model.Endpoints
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Lean Forms.Model

inductive BusinessPartnerStatus where
  | active
  | blocked (reason : String)
  deriving DecidableEq, Repr, ToJson, FromJson

structure BusinessPartnerData where
  city : String
  vatNumber : String
  status : BusinessPartnerStatus
  deriving DecidableEq, Repr, ToJson, FromJson

endpoints BusinessPartnersEndpoint where
  | search : String → LookupResults String BusinessPartnerData at "/api/business-partners"

structure BusinessPartnerSelection where
  partner : Option (Reference String)
  deriving FormModel

namespace BusinessPartners

def availability (candidate : LookupCandidate String BusinessPartnerData) : LookupAvailability :=
  match candidate.data.status with
  | .active => .enabled
  | .blocked reason => .disabled reason

def form : Component [] BusinessPartnerSelection.Raw :=
  .lookup path[BusinessPartnerSelection.Field.partner] "Business partner"
    (.const (Api.source BusinessPartnersEndpoint.search)) (.const availability)

def initial : BusinessPartnerSelection.Raw := { partner := none }

def candidates : List (LookupCandidate String BusinessPartnerData) := [
  { reference := { id := "alpine", displayText := "Alpine Supplies" }
    data := { city := "Girona", vatNumber := "VAT-100", status := .blocked "Account is blocked." } },
  { reference := { id := "barcelona", displayText := "Barcelona Office" }
    data := { city := "Barcelona", vatNumber := "VAT-200", status := .active } },
  { reference := { id := "girona", displayText := "Girona Goods" }
    data := { city := "Girona", vatNumber := "VAT-300", status := .blocked "Account is closed." } },
  { reference := { id := "vic", displayText := "Vic Components" }
    data := { city := "Vic", vatNumber := "VAT-400", status := .active } },
  { reference := { id := "legacy", displayText := "Vic Legacy" }
    data := { city := "Vic", vatNumber := "VAT-500", status := .blocked "Account is blocked." } }]

def searchText (candidate : LookupCandidate String BusinessPartnerData) : String :=
  candidate.reference.displayText ++ " " ++ candidate.data.city ++ " " ++ candidate.data.vatNumber

def mentions (text : String) (candidate : LookupCandidate String BusinessPartnerData) : Prop :=
  (searchText candidate).toLower.contains text.toLower = true

instance (text : String) : DecidablePred (mentions text) :=
  fun candidate => inferInstanceAs (Decidable ((searchText candidate).toLower.contains text.toLower = true))

def serve : HttpRequest → Option Json :=
  Api.serve (endpoint := BusinessPartnersEndpoint) fun
    | .search, (text : String) => (LookupResults.select candidates (mentions text) 5).toOption

end BusinessPartners
end Forms.ExampleForms
