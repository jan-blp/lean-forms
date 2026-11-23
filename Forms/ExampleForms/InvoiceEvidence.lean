module

public import Forms.Model.Component
public import Forms.Runtime.Viewer
public meta import Forms.Model.Derive

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

structure InvoiceHeader where
  number : String
  numberEvidence : Option Evidence
  issued : Option Std.Time.PlainDate
  issuedEvidence : Option Evidence
  total : Option Decimal
  totalEvidence : Option Evidence
  note : String
  deriving FormModel

def InvoiceHeader.form : Component [] InvoiceHeader.Raw :=
  .group "Invoice" [
    .fieldWithEvidence path[InvoiceHeader.Field.number] path[InvoiceHeader.Field.numberEvidence]
      "Invoice number" .text,
    .fieldWithEvidence path[InvoiceHeader.Field.issued] path[InvoiceHeader.Field.issuedEvidence]
      "Issued on" (.optional .date),
    .fieldWithEvidence path[InvoiceHeader.Field.total] path[InvoiceHeader.Field.totalEvidence]
      "Total" (.optional .decimal),
    .field path[InvoiceHeader.Field.note] "Internal note" .text]

/-- The number matches its cells, the date has none, and the total was mistyped. -/
def InvoiceHeader.initial : InvoiceHeader.Raw where
  number := "INV-2026-0042"
  numberEvidence := some { page := 1, cellIds := [4], text := "INV-2026-0042" }
  issued := none
  issuedEvidence := none
  total := some { mantissa := 12435, exponent := 1, normalized := by decide }
  totalEvidence := some { page := 1, cellIds := [19], text := "1234.50" }
  note := ""

def InvoiceHeader.cell (id x y width : Nat) (text : String) : Runtime.Viewer.Cell :=
  { id, x, y, width, height := 18, text }

def InvoiceHeader.document : Runtime.Viewer.Document where
  pages := [{
    number := 1
    width := 600
    height := 520
    cells := [
      InvoiceHeader.cell 0 40 40 260 "Lindenhof Office Supply GmbH",
      InvoiceHeader.cell 1 40 62 260 "Musterstraße 12, 12345 Musterstadt",
      InvoiceHeader.cell 2 440 40 120 "INVOICE",
      InvoiceHeader.cell 3 40 120 110 "Invoice no.",
      InvoiceHeader.cell 4 160 120 140 "INV-2026-0042",
      InvoiceHeader.cell 5 40 144 110 "Date",
      InvoiceHeader.cell 6 160 144 140 "2026-11-03",
      InvoiceHeader.cell 7 40 168 110 "Customer",
      InvoiceHeader.cell 8 160 168 180 "Example Retail AG",
      InvoiceHeader.cell 9 40 240 260 "Description",
      InvoiceHeader.cell 10 320 240 100 "Quantity",
      InvoiceHeader.cell 11 440 240 120 "Amount",
      InvoiceHeader.cell 12 40 266 260 "Office chairs",
      InvoiceHeader.cell 13 320 266 100 "4",
      InvoiceHeader.cell 14 440 266 120 "796.00",
      InvoiceHeader.cell 15 40 290 260 "Standing desk",
      InvoiceHeader.cell 16 320 290 100 "1",
      InvoiceHeader.cell 17 440 290 120 "438.50",
      InvoiceHeader.cell 18 320 340 100 "Total (EUR)",
      InvoiceHeader.cell 19 440 340 120 "1234.50",
      InvoiceHeader.cell 20 40 440 360 "Payment due within 30 days."] }]

end Forms.ExampleForms
