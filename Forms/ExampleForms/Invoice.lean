import Forms.Core.Form
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Invoice

abbrev itemShape : DataType := .group ![.text, .natural, .natural]
abbrev shape : DataType := .list itemShape

def positive : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .natLe (.value 1) (.project .here)
      errorMessage := "Quantity and unit price must be at least 1."
      errorLocation := some ⟨.here⟩ }

def itemType : RefinedDataType itemShape :=
  .group fun
    | 0 => .base .text
    | 1 => positive
    | 2 => positive

def invoiceType : RefinedDataType shape := .list itemType

def newItem : itemType.denote := fun
  | 0 => "New item"
  | 1 => ⟨(1 : Nat), by decide⟩
  | 2 => ⟨(100 : Nat), by decide⟩

def initial : invoiceType.denote := [newItem]
def draft : shape.denote := invoiceType.erase initial

def itemForm : Form itemShape itemShape :=
  .group "Item" fun
    | 0 => .field "Description" .textInput
    | 1 => .field "Quantity" .naturalInput
    | 2 => .field "Unit price (cents)" .naturalInput

def form : Form shape shape := .list "Invoice" itemForm (itemType.erase newItem)

end Forms.ExampleForms.Invoice
