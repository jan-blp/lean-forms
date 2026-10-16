import Forms.Core.Form

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

def newItem : DataType.denote itemShape
  | .description => "New item"
  | .quantity => 1
  | .unitPrice => 100

def initial : DataType.denote shape := [newItem]

def itemForm : Form itemShape itemShape :=
  .group "Item" fun
    | .description => .field "Description" .textInput
    | .quantity => .field "Quantity" .naturalInput
    | .unitPrice => .field "Unit price (cents)" .naturalInput

def form : Form shape shape := .list "Invoice" itemForm newItem

end Forms.ExampleForms.Invoice
