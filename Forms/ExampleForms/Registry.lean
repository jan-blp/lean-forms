module

public import Forms.ExampleForms.Person
public import Forms.ExampleForms.Order
public import Forms.ExampleForms.Expenses
public import Forms.ExampleForms.Invoice
public import Forms.Runtime.FormDefinition
public import Std.Data.HashMap

@[expose] public section
namespace Forms.ExampleForms
open Forms.Runtime

/-- Forms of the example application, shared by its native and Wasm builds; the first is the default. -/
def forms : List (String × RegisteredForm) := [
  ("person", { definition := .ofModel Person Person.form Person.initial, submitUrl := "/api/submit" }),
  ("order", { definition := .ofModel Order Order.form Order.initial, submitUrl := "/api/submit" }),
  ("expenses", {
    definition := .ofModel ExpenseReport ExpenseReport.form ExpenseReport.initial
    submitUrl := "/api/submit" }),
  ("invoice", { definition := .ofModel Invoice Invoice.form Invoice.initial, submitUrl := "/api/submit" })]

/-- Responses of the example application's data endpoints. -/
def api : Model.HttpRequest → Option Lean.Json :=
  Model.Api.serve SupplierEndpoint.fixture

def registeredForms : Std.HashMap String RegisteredForm := .ofList forms

end Forms.ExampleForms
