module

public import Forms.Model.Component
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

structure Payment where
  amount : Decimal
  dueDate : Std.Time.PlainDate
  reference : Uuid
  adjustment : Int32
  ledgerEntry : Int64
  deriving FormModel

def Payment.form : Component [] Payment.Raw :=
  .group "Payment" [
    .field path[Payment.Field.amount] "Amount" .decimal,
    .field path[Payment.Field.dueDate] "Due date" .date,
    .field path[Payment.Field.reference] "Reference" .uuid,
    .field path[Payment.Field.adjustment] "Adjustment" .int32,
    .field path[Payment.Field.ledgerEntry] "Ledger entry" .int64]

def Payment.initial : Payment.Raw := ⟨
  ⟨1255, 1, by decide⟩,
  .ofYearMonthDayClip 2026 11 15,
  ⟨"123e4567-e89b-12d3-a456-426614174000", by decide⟩,
  -5,
  9007199254740993⟩

end Forms.ExampleForms
