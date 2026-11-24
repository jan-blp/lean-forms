module

public import Forms.ExampleForms.Person
public import Forms.ExampleForms.Order
public import Forms.ExampleForms.Expenses
public import Forms.ExampleForms.Projects
public import Forms.ExampleForms.SharedState
public import Forms.ExampleForms.Outputs
public import Forms.ExampleForms.Presentation
public import Forms.ExampleForms.Scalars
public import Forms.ExampleForms.Selections
public import Forms.ExampleForms.Navigation
public import Forms.ExampleForms.PaymentMethod
public import Forms.ExampleForms.Receipts
public import Forms.ExampleForms.InvoiceEvidence
public import Forms.ExampleForms.Delivery
public import Forms.ExampleForms.BusinessPartners
public import Forms.Runtime.FormDefinition
public import Std.Data.HashMap

@[expose] public section
namespace Forms.ExampleForms
open Forms.Runtime Forms.Model

def paymentMethod : RegisteredForm where
  definition := .ofModel PaymentMethod PaymentMethod.form PaymentMethod.initial
  submitUrl := "/api/submit"

def receipts : RegisteredForm where
  definition := .ofModel Receipts Receipts.form Receipts.initial
  submitUrl := "/api/submit"

/-- The first is the default. -/
def forms : List (String × RegisteredForm) := [
  ("person", {
    definition := .ofModel Person Person.form Person.initial
    submitUrl := "/api/submit" }),
  ("order", {
    definition := .ofModel Order Order.form Order.initial
    submitUrl := "/api/submit" }),
  ("expenses", {
    definition := .ofModel ExpenseReport ExpenseReport.focusForm ExpenseReport.initial
    submitUrl := "/api/submit" }),
  ("projects", {
    definition := .ofModel ProjectPlanner ProjectPlanner.form ProjectPlanner.initial
    submitUrl := "/api/submit" }),
  ("shared-state", {
    definition := .ofModel (Collection Nat) SharedState.form SharedState.initial
    submitUrl := "/api/submit" }),
  ("outputs", {
    definition := .ofModel Nat Outputs.single 10
    submitUrl := "/api/submit" }),
  ("nested-outputs", {
    definition := .ofModel (Collection Nat) Outputs.nested Outputs.initial
    submitUrl := "/api/submit" }),
  ("present-table", {
    definition := .ofModel (Collection String) Presentation.tableSummary Outputs.descriptions
     
    submitUrl := "/api/submit" }),
  ("present-tabs", {
    definition := .ofModel Nat Presentation.sharedTabs 0
    submitUrl := "/api/submit" }),
  ("present-notes", {
    definition := .ofModel (Collection String) Presentation.notes Presentation.initialNotes
     
    submitUrl := "/api/submit" }),
  ("scalars", {
    definition := .ofModel Payment Payment.form Payment.initial
    submitUrl := "/api/submit" }),
  ("navigation", {
    definition := .ofModel Person Navigation.form Navigation.initial
    submitUrl := "/api/submit" }),
  ("selections", {
    definition := .ofModel Preferences Preferences.form Preferences.initial
    submitUrl := "/api/submit" }),
  ("payment-method", paymentMethod),
  ("receipts", receipts),
  ("evidence", {
    definition := .ofModel InvoiceHeader InvoiceHeader.form InvoiceHeader.initial
    submitUrl := "/api/submit" }),
  ("delivery", {
    definition := .ofModel Delivery Delivery.form Delivery.initial
    submitUrl := "/api/submit" }),
  ("business-partners", {
    definition := .ofModel BusinessPartnerSelection BusinessPartners.form BusinessPartners.initial
    submitUrl := "/api/submit" })]

def api (request : Model.HttpRequest) : Option Lean.Json :=
  (Delivery.serve request).orElse fun () => BusinessPartners.serve request

def registeredForms : Std.HashMap String RegisteredForm := .ofList forms

end Forms.ExampleForms
