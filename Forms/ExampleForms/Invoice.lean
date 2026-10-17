import Forms.Core.Component.Builder
import Forms.Core.RefinedDataType

namespace Forms.ExampleForms.Invoice
open Composition

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

abbrev item : DataType := .record itemFields fun
  | .description => .text
  | .quantity | .unitPrice => .natural
abbrev invoice : DataType := .list item

def positive : RefinedDataType .natural :=
  .refine (.base .natural)
    { condition := .natLe (.value 1) (.project .self)
      errorMessage := "Quantity and unit price must be at least 1."
      errorLocation := some ⟨.self⟩ }

def itemType : RefinedDataType item :=
  .record fun
    | .description => .base .text
    | .quantity | .unitPrice => positive

def invoiceType : RefinedDataType invoice := .list itemType

def newItem : RefinedDataType.ValidatedValue itemType
  | .description => "New item"
  | .quantity => ⟨(1 : Nat), by decide⟩
  | .unitPrice => ⟨(100 : Nat), by decide⟩

def initial : RefinedDataType.ValidatedValue invoiceType := [newItem]
def draft : ⟦invoice⟧ := RefinedDataType.erase invoiceType initial

def subtotal : Expr item .natural :=
  .natMul (.project (.field .quantity .self)) (.project (.field .unitPrice .self))

def itemForm : Component item :=
  (show Component.Builder item item from
    Component.Builder.computed "Subtotal (cents)" subtotal
      (Component.Builder.group "Item" fun
        | .description => Component.Builder.field "Description" .textInput
        | .quantity => Component.Builder.field "Quantity" .naturalInput
        | .unitPrice => Component.Builder.field "Unit price (cents)" .naturalInput)) .self

def total : Expr invoice .natural := .sum (.project .self) subtotal

def form : Component invoice :=
  (show Component.Builder invoice invoice from
    Component.Builder.computed "Total (cents)" total
      (Component.Builder.list "Invoice" (fun _ => itemForm) (RefinedDataType.erase itemType newItem))) .self

end Forms.ExampleForms.Invoice
