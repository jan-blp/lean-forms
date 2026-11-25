module

public import Forms.Model.Configuration
public meta import Forms.Model.Derive
public meta import Forms.Deriving.FinEnum

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

structure SupplierAddress where
  street : String
  city : String
  deriving FormModel

structure TenantInvoice where
  number : String
  supplier : String
  reference : String
  vatDate : Option Std.Time.PlainDate
  postingDate : Option Std.Time.PlainDate
  address : SupplierAddress
  number_valid : number ≠ ""
  reference_valid : reference ≠ ""
  deriving FormModel

instance : ConstraintRule TenantInvoice.Constraint.number_valid where
  check parts :=
    if h : parts.number ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter the invoice number.")
      (targets := locations[TenantInvoice.Field.number])

instance : ConstraintRule TenantInvoice.Constraint.reference_valid where
  check parts :=
    if h : parts.reference ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter the reference.")
      (targets := locations[TenantInvoice.Field.reference])

inductive SupplierAddress.Configurable where
  | city
  deriving DecidableEq

def SupplierAddress.form {Γ : Context} : Configured Γ SupplierAddress.Raw SupplierAddress.Configurable :=
  .group "Supplier address" [
    .fixed (.field path[SupplierAddress.Field.street] "Street" .text),
    .configurable .city "City" path[SupplierAddress.Field.city]
      (.allowed (.reset "") .shown) (lockable := false)
      (.field path[SupplierAddress.Field.city] "City" .text)]

inductive TenantInvoice.Configurable where
  | supplier
  | reference
  | vatDate
  | postingDate
  | city
  deriving DecidableEq, FinEnum

/-- Stored in settings: renaming a constructor keeps these. -/
def TenantInvoice.Configurable.encode : TenantInvoice.Configurable → String
  | .supplier => "supplier"
  | .reference => "reference"
  | .vatDate => "vatDate"
  | .postingDate => "postingDate"
  | .city => "city"

instance : Key TenantInvoice.Configurable :=
  .ofSorted [.city, .postingDate, .reference, .supplier, .vatDate]
    TenantInvoice.Configurable.encode
    (by intro key; cases key <;> decide)
    (by decide)
    (by decide)

def TenantInvoice.form {Γ : Context} : Configured Γ TenantInvoice.Raw TenantInvoice.Configurable :=
  .group "Invoice" [
    .fixed (.field path[TenantInvoice.Field.number] "Invoice number" .text),
    .configurable .supplier "Supplier" path[TenantInvoice.Field.supplier]
      .forbidden (lockable := true)
      (.field path[TenantInvoice.Field.supplier] "Supplier" .text),
    .configurable .reference "Reference" path[TenantInvoice.Field.reference]
      (.allowed .keep .shown) (lockable := true)
      (.field path[TenantInvoice.Field.reference] "Reference" .text),
    .configurable .vatDate "VAT date" path[TenantInvoice.Field.vatDate]
      (.allowed (.reset none) .shown) (lockable := true)
      (.field path[TenantInvoice.Field.vatDate] "VAT date" (.optional .date)),
    .configurable .postingDate "Posting date" path[TenantInvoice.Field.postingDate]
      (.allowed .keep .excluded) (lockable := false)
      (.field path[TenantInvoice.Field.postingDate] "Posting date" (.optional .date)),
    .nested <| .zoom path[TenantInvoice.Field.address] <|
      .mapKey (fun | .city => TenantInvoice.Configurable.city) SupplierAddress.form]

def TenantInvoice.initial : TenantInvoice.Raw := {
  number := "INV-1"
  supplier := "Acme"
  reference := "PO-7"
  vatDate := some (.ofYearMonthDayClip 2026 11 15)
  postingDate := none
  address := { street := "Main Street 1", city := "Girona" } }

/-- Moves the posting date first, locks the supplier, and excludes the reference, the VAT date
and the city. `legacyField` is unknown and ignored. -/
def TenantInvoice.tenantSettings : Settings where
  fields := [
    { key := "postingDate", state := .shown },
    { key := "supplier", state := .readOnly },
    { key := "reference", state := .excluded },
    { key := "vatDate", state := .excluded },
    { key := "city", state := .excluded },
    { key := "legacyField", state := .shown }]

end Forms.ExampleForms
