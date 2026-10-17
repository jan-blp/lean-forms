import Forms.Core.Form
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Invoice

inductive ItemField where
  | description | quantity | unitPrice
  deriving DecidableEq, Repr

instance : FinEnum ItemField :=
  FinEnum.ofList [.description, .quantity, .unitPrice] (by grind [ItemField])

def itemFields : Enum where
  type := ItemField
  label
    | .description => "description"
    | .quantity => "quantity"
    | .unitPrice => "unitPrice"

abbrev itemShape : DataType := .record itemFields fun
  | .description => .text
  | .quantity | .unitPrice => .natural
abbrev shape : DataType := .list itemShape

def positive : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .natLe (.value 1) (.project .self)
      errorMessage := "Quantity and unit price must be at least 1."
      errorLocation := some ⟨.self⟩ }

def itemType : RefinedDataType itemShape :=
  .record fun
    | .description => .base .text
    | .quantity | .unitPrice => positive

def invoiceType : RefinedDataType shape := .list itemType

def newItem : RefinedDataType.ValidatedValue itemType
  | .description => "New item"
  | .quantity => ⟨(1 : Nat), by decide⟩
  | .unitPrice => ⟨(100 : Nat), by decide⟩

def initial : RefinedDataType.ValidatedValue invoiceType := [newItem]
def draft : DataType.denote shape := RefinedDataType.erase invoiceType initial

def subtotal : Expr itemShape .natural :=
  .natMul (.project (.child .quantity .self)) (.project (.child .unitPrice .self))

def itemForm : Form itemShape itemShape :=
  .computed "Subtotal (cents)" subtotal
    (.group "Item" fun
      | .description => .field "Description" .textInput
      | .quantity => .field "Quantity" .naturalInput
      | .unitPrice => .field "Unit price (cents)" .naturalInput)

def total : Expr shape .natural := .sum (.project .self) subtotal

def form : Form shape shape :=
  .computed "Total (cents)" total
    (.list "Invoice" itemForm (RefinedDataType.erase itemType newItem))

end Forms.ExampleForms.Invoice
