module

public import Forms.Model.Component
public import Forms.ExampleForms.Format
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

/-! Rules are named: auto-generated names can clash with other example forms. -/

structure Expense where
  description : String
  amount : Nat
  receipt : Bool
  description_valid : description ≠ ""
  amount_valid : 1 ≤ amount
  receipt_valid : 100 ≤ amount → receipt = true
  deriving FormModel

instance Expense.description_valid_rule : ConstraintRule Expense.Constraint.description_valid where
  check parts :=
    if h : parts.description ≠ "" then .valid h
    else .invalid (proof := h) (message := "Describe the expense.")
      (targets := locations[Expense.Field.description])

instance Expense.amount_valid_rule : ConstraintRule Expense.Constraint.amount_valid where
  check parts :=
    if h : 1 ≤ parts.amount then .valid h
    else .invalid (proof := h) (message := "Enter an amount of at least CHF 1.")
      (targets := locations[Expense.Field.amount])

instance Expense.receipt_valid_rule : ConstraintRule Expense.Constraint.receipt_valid where
  check parts :=
    if h : 100 ≤ parts.amount → parts.receipt = true then .valid h
    else .invalid (proof := h) (message := "Attach a receipt for CHF 100 or more.")
      (targets := locations[Expense.Field.receipt])

structure ExpenseReport where
  employee : String
  expenses : List Expense
  employee_valid : employee ≠ ""
  expenses_valid : 0 < expenses.length
  limit_valid : (expenses.map (·.amount)).sum ≤ 5000
  deriving FormModel

instance ExpenseReport.employee_valid_rule
  : ConstraintRule ExpenseReport.Constraint.employee_valid where
  check parts :=
    if h : parts.employee ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter the employee name.")
      (targets := locations[ExpenseReport.Field.employee])

instance ExpenseReport.expenses_valid_rule
  : ConstraintRule ExpenseReport.Constraint.expenses_valid where
  check parts :=
    if h : 0 < parts.expenses.length then .valid h
    else .invalid (proof := h) (message := "Add at least one expense.")
      (targets := locations[ExpenseReport.Field.expenses])

instance ExpenseReport.limit_valid_rule : ConstraintRule ExpenseReport.Constraint.limit_valid where
  check parts :=
    if h : (parts.expenses.map (·.amount)).sum ≤ 5000 then .valid h
    else .invalid (proof := h) (message := "A report is limited to CHF 5'000.")
      (targets := locations[ExpenseReport.Field.expenses])

def ExpenseReport.initial : ExpenseReport.Raw :=
  ⟨"Ada Lovelace", [⟨"Train to Bern", 58, false⟩, ⟨"Hotel", 180, true⟩]⟩

def Expense.columns {Γ : Context} : Columns Γ Expense.Raw := columns[
  "Description" => .field
    (path := path[Expense.Field.description]) (label := "Description") (editor := .text),
  "Amount (CHF)" => .field
    (path := path[Expense.Field.amount]) (label := "Amount (CHF)") (editor := .natural),
  "Receipt" => .visibleWhen
    (condition := {
      inputs := inputs[path[Expense.Field.amount]]
      run := fun amount => decide (100 ≤ amount)
    })
    (body := .field
      (path := path[Expense.Field.receipt]) (label := "Receipt attached") (editor := .checkbox))]

def ExpenseReport.withItems {Γ : Context} (items : Component Γ ExpenseReport.Raw) : Component Γ ExpenseReport.Raw :=
  .group (label := "Expense report") (children := [
    .field
      (path := path[ExpenseReport.Field.employee])
      (label := "Employee")
      (editor := .text),
    items,
    .computed
      (label := "Total")
      (value := {
        inputs := inputs[path[ExpenseReport.Field.expenses]]
        run := fun expenses => s!"CHF {swiss (expenses.map (·.amount)).sum}"
      })])

def ExpenseReport.listForm {Γ : Context} : Component Γ ExpenseReport.Raw :=
  ExpenseReport.withItems (.list
    (path := path[ExpenseReport.Field.expenses])
    (label := "Expenses")
    (itemLabel := "Expense")
    (initial := ⟨"", 0, false⟩)
    (body := .groupOf (label := "") (children := Expense.columns.components)))

def ExpenseReport.form {Γ : Context} : Component Γ ExpenseReport.Raw :=
  ExpenseReport.withItems (.table
    (path := path[ExpenseReport.Field.expenses])
    (label := "Expenses")
    (itemLabel := "Expense")
    (initial := ⟨"", 0, false⟩)
    (columns := Expense.columns))

def ExpenseReport.focusForm : Component [] ExpenseReport.Raw :=
  .bind RowSelection.none (.group (label := "Expense report") (children := [
    .field
      (path := path[ExpenseReport.Field.employee])
      (label := "Employee") (editor := .text),
    .table
      (path := path[ExpenseReport.Field.expenses])
      (label := "Expenses")
      (itemLabel := "Expense")
      (initial := ⟨"", 0, false⟩)
      (columns := columns[
        "Description" => .computed "Description" {
          inputs := inputs[path[Expense.Field.description]], run := id },
        "Amount (CHF)" => .computed "Amount (CHF)" {
          inputs := inputs[path[Expense.Field.amount]], run := fun amount => s!"CHF {swiss amount}" },
        "Receipt" => .computed "Receipt" {
          inputs := inputs[path[Expense.Field.receipt]], run := fun receipt => if receipt then "Yes" else "No" }])
      (selection := some .here),
    .focus
      (target := {
        inputs := inputs[.ui .here]
        run := RowSelection.itemPath path[ExpenseReport.Field.expenses]
      })
      (body := .groupOf (label := "Selected expense") (children := Expense.columns.components)),
    .computed (label := "Total") (value := {
      inputs := inputs[path[ExpenseReport.Field.expenses]]
      run := fun expenses => s!"CHF {swiss (expenses.map (·.amount)).sum}"
    })]))

end Forms.ExampleForms
