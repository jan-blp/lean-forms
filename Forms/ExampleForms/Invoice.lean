module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Lean Forms.Model

structure SupplierDetails where
  contacts : List (KeyedOption String)
  requiresPurchaseOrder : Bool
  deriving ToJson, FromJson

inductive SupplierEndpoint where
  | suppliers
  | supplier
  deriving DecidableEq, Repr

def SupplierEndpoint.Input : SupplierEndpoint → Type
  | .suppliers => Unit
  | .supplier => String

def SupplierEndpoint.Output : SupplierEndpoint → Type
  | .suppliers => List (KeyedOption String)
  | .supplier => SupplierDetails

instance : Api SupplierEndpoint where
  Input := SupplierEndpoint.Input
  Output := SupplierEndpoint.Output
  path
    | .suppliers => "/api/suppliers"
    | .supplier => "/api/supplier"
  all := [.suppliers, .supplier]
  complete := by
    intro named
    cases named <;> decide
  distinct := by decide
  inputToJson
    | .suppliers => inferInstanceAs (ToJson Unit)
    | .supplier => inferInstanceAs (ToJson String)
  inputFromJson
    | .suppliers => inferInstanceAs (FromJson Unit)
    | .supplier => inferInstanceAs (FromJson String)
  outputToJson
    | .suppliers => inferInstanceAs (ToJson (List (KeyedOption String)))
    | .supplier => inferInstanceAs (ToJson SupplierDetails)
  outputFromJson
    | .suppliers => inferInstanceAs (FromJson (List (KeyedOption String)))
    | .supplier => inferInstanceAs (FromJson SupplierDetails)

def supplierDetails : String → Option SupplierDetails
  | "acme" => some ⟨[⟨"anna", "Anna Muster"⟩, ⟨"ben", "Ben Keller"⟩], true⟩
  | "globex" => some ⟨[⟨"carla", "Carla Rossi"⟩], false⟩
  | "initech" => some ⟨[], true⟩
  | _ => none

def SupplierEndpoint.fixture : (named : SupplierEndpoint) → named.Input → Option named.Output
  | .suppliers, _ => some [⟨"acme", "ACME AG"⟩, ⟨"globex", "Globex GmbH"⟩, ⟨"initech", "Initech Ltd"⟩]
  | .supplier, id => supplierDetails id

structure SupplierPart where
  contact : Selected String Unit
  purchaseOrder : String
  deriving FormModel

structure Invoice where
  supplier : Selected String SupplierPart
  amount : Nat
  supplier_valid : supplier.selected.isSome = true
  amount_valid : 1 ≤ amount
  deriving FormModel

instance Invoice.supplier_valid_rule : ConstraintRule Invoice.Constraint.supplier_valid where
  check parts :=
    if h : parts.supplier.selected.isSome = true then .valid h
    else .invalid (proof := h) (message := "Choose a supplier.")
      (targets := locations[Invoice.Field.supplier])

instance Invoice.amount_valid_rule : ConstraintRule Invoice.Constraint.amount_valid where
  check parts :=
    if h : 1 ≤ parts.amount then .valid h
    else .invalid (proof := h) (message := "Enter an amount of at least CHF 1.")
      (targets := locations[Invoice.Field.amount])

def Invoice.initial : Invoice.Raw := ⟨.empty, 250⟩

def Invoice.form : Component Invoice.Raw :=
  .group (label := "Invoice") (children := [
    .load
      (source := .const (Api.source SupplierEndpoint.suppliers ()))
      (body := .keyed
        (path := path[Scope.Field.value, Invoice.Field.supplier])
        (label := "Supplier")
        (options := { inputs := inputs[path[Scope.Field.context]], run := id })
        (initial := ⟨.empty, ""⟩)
        (body := .load
          (source := {
            inputs := inputs[path[Scope.Field.context]]
            run := Api.source SupplierEndpoint.supplier
          })
          (body := .group (label := "") (children := [
            .keyed
              (path := path[Scope.Field.value, Scope.Field.value, SupplierPart.Field.contact])
              (label := "Contact")
              (options := { inputs := inputs[path[Scope.Field.context]], run := (·.contacts) })
              (initial := ())
              (body := .group (label := "") (children := [])),
            .visibleWhen
              (condition := {
                inputs := inputs[path[Scope.Field.context]]
                run := (·.requiresPurchaseOrder)
              })
              (body := .field
                (path :=
                  path[Scope.Field.value, Scope.Field.value, SupplierPart.Field.purchaseOrder])
                (label := "Purchase order")
                (editor := .text))])))),
    .field
      (path := path[Invoice.Field.amount])
      (label := "Amount (CHF)")
      (editor := .natural)])

end Forms.ExampleForms
