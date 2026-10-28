import Forms.ExampleForms.Invoice
import Forms.Runtime.FormSnapshot

namespace Forms.Presentation.Lists

open Composition
open Forms.ExampleForms.Invoice (itemFields)

abbrev item : DataType := .record itemFields fun
  | .description => .text
  | .quantity | .unitPrice => .natural

def itemForm : Component item :=
  .stack (some "Item") (items := itemFields) (fun
    | .description =>
        .field (.field .description .self) "Description" .textInput
    | .quantity =>
        .field (.field .quantity .self) "Quantity" .naturalInput
    | .unitPrice =>
        .field (.field .unitPrice .self) "Unit price (cents)" .naturalInput)

abbrev invoice : DataType := .list item

def newItem : ⟦item⟧
  | .description => "New item"
  | .quantity => 1
  | .unitPrice => 100

def initial : ⟦invoice⟧ := [newItem]

def form : Component invoice :=
  .list .self "Invoice" itemForm newItem

#guard (Runtime.FormSnapshot.render form initial).fieldRefs.length == 3

end Forms.Presentation.Lists
