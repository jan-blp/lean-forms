module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

@[report_rule] structure Receipt where
  number : String
  alreadySubmitted : ReadOnly Bool
  number_valid : number ≠ ""
  deriving FormModel

instance Receipt.number_valid_rule : ConstraintRule Receipt.Constraint.number_valid where
  check parts :=
    if h : parts.number ≠ "" then .valid h
    else .invalid (proof := h) (message := "Enter the receipt number.")
      (targets := locations[Receipt.Field.number])

instance : ReportRule Receipt where
  reports raw :=
    if raw.alreadySubmitted.value then
      [{ status := .unresolved
         severity := .warning
         message := "This receipt was already submitted."
         targets := .locations (.field Receipt.Field.number .self) }]
    else []

structure Receipts where
  receipts : Collection Receipt
  numbers_distinct : (receipts.values.map (·.number)).Nodup
  deriving FormModel

instance Receipts.numbers_distinct_rule : ConstraintRule Receipts.Constraint.numbers_distinct where
  check parts :=
    if h : (parts.receipts.values.map (fun receipt : Receipt => receipt.number)).Nodup then .valid h
    else
      let raw := Receipts.Parts.toRaw parts
      let repeated := raw.receipts.entries.attach.filterMap fun ⟨entry, member⟩ =>
        if (raw.receipts.values.filter (·.number == entry.value.number)).length > 1 then
          some (.field Receipts.Field.receipts
            (.item entry member (.field Receipt.Field.number .self)))
        else none
      let message := "Another receipt in this form has the same number."
      match repeated with
      | [] => .invalid (proof := h) (message := message) (targets := .global)
      | first :: rest =>
        .invalid (proof := h) (message := message) (targets := .locations first rest)

def Receipts.form : Component [] Receipts.Raw :=
  Component.void <| .list
    (path := path[Receipts.Field.receipts])
    (label := "Receipts")
    (rowLabel := .numbered "Receipt")
    (addCaption := "Add receipt")
    (initial := { number := "", alreadySubmitted := ⟨false⟩ })
    (body := .group "" [
      .statusMarkerAt path[Receipt.Field.number],
      .field path[Receipt.Field.number] "Receipt number" .text])

def Receipts.initial : Receipts.Raw where
  receipts := .numbered [{ number := "R-1001", alreadySubmitted := ⟨false⟩ }]

end Forms.ExampleForms
