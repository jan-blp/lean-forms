module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

@[report_rule] structure Receipt where
  id : Uuid
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
      [{ message := "This receipt was already submitted."
         targets := .locations (.field Receipt.Field.number .self) }]
    else []

deriving instance HasUuid for Receipt.Raw

@[report_rule] structure Receipts where
  receipts : List Receipt
  deriving FormModel

instance : ReportRule Receipts where
  reports raw := raw.receipts.attach.filterMap fun ⟨receipt, member⟩ =>
    if (raw.receipts.filter (·.number == receipt.number)).length > 1 then
      some
        { message := "Another receipt in this form has the same number."
          targets := .locations (.field Receipts.Field.receipts
            (.item receipt member (.field Receipt.Field.number .self))) }
    else none

def Receipts.form : Component [] Receipts.Raw :=
  Component.void <| .list
    (path := path[Receipts.Field.receipts])
    (label := "Receipts")
    (rowLabel := .numbered "Receipt")
    (addCaption := "Add receipt")
    (initial := Receipt.Raw.mkWithoutUuid (number := "") (alreadySubmitted := ⟨false⟩))
    (body := .field path[Receipt.Field.number] "Receipt number" .text)

def Receipts.initial : Receipts.Raw :=
  IdGen.run do
    pure ⟨[⟨← freshId, "R-1001", ⟨false⟩⟩]⟩

end Forms.ExampleForms
