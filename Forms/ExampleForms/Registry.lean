module

public import Forms.ExampleForms.Person
public import Forms.ExampleForms.Order
public import Forms.ExampleForms.Expenses
public import Forms.ExampleForms.Projects
public import Forms.ExampleForms.SharedState
public import Forms.ExampleForms.Outputs
public import Forms.ExampleForms.Presentation
public import Forms.Runtime.FormDefinition
public import Std.Data.HashMap

@[expose] public section
namespace Forms.ExampleForms
open Forms.Runtime Forms.Model

/-- Forms of the example application, shared by its native and Wasm builds; the first is the default. -/
def forms : List (String × RegisteredForm) := [
  ("person", { definition := .ofModel Person Person.form Person.initial, submitUrl := "/api/submit" }),
  ("order", { definition := .ofModel Order Order.form Order.initial, submitUrl := "/api/submit" }),
  ("expenses", {
    definition := .ofModel ExpenseReport ExpenseReport.focusForm ExpenseReport.initial
    submitUrl := "/api/submit" }),
  ("projects", {
    definition := .ofModel ProjectPlanner ProjectPlanner.form ProjectPlanner.initial
    submitUrl := "/api/submit" }),
  ("shared-state", {
    definition := .ofModel (List Nat) SharedState.form SharedState.initial
    submitUrl := "/api/submit" }),
  ("outputs", {
    definition := .ofModel Nat Outputs.single 10
    submitUrl := "/api/submit" }),
  ("row-outputs", {
    definition := .ofModel (List Nat) Outputs.repeated Outputs.initial
    submitUrl := "/api/submit" }),
  ("nested-outputs", {
    definition := .ofModel (List Nat) Outputs.nested Outputs.initial
    submitUrl := "/api/submit" }),
  ("table-outputs", {
    definition := .ofModel (List String) Outputs.selectedDescriptions ["Same description", "Same description", "Another item"]
    submitUrl := "/api/submit" }),
  ("present-table", {
    definition := .ofModel (List String) Presentation.tableSummary
      ["Same description", "Same description", "Another item"]
    submitUrl := "/api/submit" }),
  ("present-tabs", {
    definition := .ofModel Nat Presentation.sharedTabs 0
    submitUrl := "/api/submit" }),
  ("present-notes", {
    definition := .ofModel (List String) Presentation.notes ["First note", "Second note"]
    submitUrl := "/api/submit" })]

/-- Responses of the example application's data endpoints; it has none. -/
def api : Model.HttpRequest → Option Lean.Json :=
  fun _ => none

def registeredForms : Std.HashMap String RegisteredForm := .ofList forms

end Forms.ExampleForms
