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
public import Forms.Runtime.FormDefinition
public import Std.Data.HashMap

@[expose] public section
namespace Forms.ExampleForms
open Forms.Runtime Forms.Model

/-- The first is the default. -/
def forms : List (String × RegisteredForm) := [
  ("person", {
    definition := .ofModel Person Person.form Person.initial (store := id)
    submitUrl := "/api/submit" }),
  ("order", {
    definition := .ofModel Order Order.form Order.initial (store := id)
    submitUrl := "/api/submit" }),
  ("expenses", {
    definition := .ofModel ExpenseReport ExpenseReport.focusForm ExpenseReport.initial (store := id)
    submitUrl := "/api/submit" }),
  ("projects", {
    definition := .ofModel ProjectPlanner ProjectPlanner.form ProjectPlanner.initial (store := id)
    submitUrl := "/api/submit" }),
  ("shared-state", {
    definition := .ofModel (List (Item Nat)) SharedState.form SharedState.initial (store := id)
    submitUrl := "/api/submit" }),
  ("outputs", {
    definition := .ofModel Nat Outputs.single 10 (store := id)
    submitUrl := "/api/submit" }),
  ("nested-outputs", {
    definition := .ofModel (List (Item Nat)) Outputs.nested Outputs.initial (store := id)
    submitUrl := "/api/submit" }),
  ("present-table", {
    definition := .ofModel (List (Item String)) Presentation.tableSummary Outputs.descriptions
      (store := id)
    submitUrl := "/api/submit" }),
  ("present-tabs", {
    definition := .ofModel Nat Presentation.sharedTabs 0 (store := id)
    submitUrl := "/api/submit" }),
  ("present-notes", {
    definition := .ofModel (List (Item String)) Presentation.notes Presentation.initialNotes
      (store := id)
    submitUrl := "/api/submit" }),
  ("scalars", {
    definition := .ofModel Payment Payment.form Payment.initial (store := id)
    submitUrl := "/api/submit" }),
  ("navigation", {
    definition := .ofModel Person Navigation.form Navigation.initial (store := id)
    submitUrl := "/api/submit" }),
  ("selections", {
    definition := .ofModel Preferences Preferences.form Preferences.initial (store := id)
    submitUrl := "/api/submit" }),
  ("payment-method", {
    definition := .ofModel PaymentMethod PaymentMethod.form PaymentMethod.initial
      (store := PaymentMethod.serverCheck)
    submitUrl := "/api/submit" })]

def api : Model.HttpRequest → Option Lean.Json :=
  fun _ => none

def registeredForms : Std.HashMap String RegisteredForm := .ofList forms

end Forms.ExampleForms
