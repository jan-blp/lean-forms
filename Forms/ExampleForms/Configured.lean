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

inductive SupplierAddress.FieldKey where
  | city
  deriving DecidableEq, FinEnum

instance : FieldKey SupplierAddress.FieldKey where
  toKey := .ofFinEnum fun
    | .city => "city"

instance : FieldPaths SupplierAddress.Raw SupplierAddress.FieldKey where
  Field
    | .city => String
  path
    | .city => path[SupplierAddress.Field.city]

def SupplierAddress.form {Γ : Context} : Configured Γ SupplierAddress.Raw SupplierAddress.FieldKey :=
  .group "Supplier address" [
    .fixed (.field path[SupplierAddress.Field.street] "Street" .text),
    .field .city "City" .text (.allowed (.reset "") .shown) (lockable := false)]

inductive TenantInvoice.FieldKey where
  | supplier
  | reference
  | vatDate
  | postingDate
  | address (key : SupplierAddress.FieldKey)
  deriving DecidableEq, FinEnum

instance : FieldKey TenantInvoice.FieldKey where
  toKey := .ofFinEnum fun
    | .supplier => "supplier"
    | .reference => "reference"
    | .vatDate => "vatDate"
    | .postingDate => "postingDate"
    | .address key => "address." ++ Key.encode key

instance : FieldPaths TenantInvoice.Raw TenantInvoice.FieldKey where
  Field
    | .supplier => String
    | .reference => String
    | .vatDate => Option Std.Time.PlainDate
    | .postingDate => Option Std.Time.PlainDate
    | .address key => FieldPaths.Field SupplierAddress.Raw key
  path
    | .supplier => path[TenantInvoice.Field.supplier]
    | .reference => path[TenantInvoice.Field.reference]
    | .vatDate => path[TenantInvoice.Field.vatDate]
    | .postingDate => path[TenantInvoice.Field.postingDate]
    | .address key => path[TenantInvoice.Field.address].trans (FieldPaths.path key)

def TenantInvoice.form {Γ : Context} : Configured Γ TenantInvoice.Raw TenantInvoice.FieldKey :=
  .group "Invoice" [
    .fixed (.field path[TenantInvoice.Field.number] "Invoice number" .text),
    .field .supplier "Supplier" .text .forbidden (lockable := true),
    .field .reference "Reference" .text (.allowed .keep .shown) (lockable := true),
    .field .vatDate "VAT date" (.optional .date) (.allowed (.reset none) .shown) (lockable := true),
    .field .postingDate "Posting date" (.optional .date) (.allowed .keep .excluded) (lockable := false),
    .nested (.nest .address path[TenantInvoice.Field.address] SupplierAddress.form)]

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
    { key := "address.city", state := .excluded },
    { key := "legacyField", state := .shown }]

end Forms.ExampleForms
