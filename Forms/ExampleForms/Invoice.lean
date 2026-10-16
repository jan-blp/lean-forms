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

abbrev item : DataType := .record itemFields fun
  | .description => .text
  | .quantity | .unitPrice => .natural
abbrev invoice : DataType := .list item

def newItem : DataType.denote item
  | .description => "New item"
  | .quantity => 1
  | .unitPrice => 100

def initial : DataType.denote invoice := [newItem]

def itemForm : Form item item :=
  .group "Item" fun
    | .description => .field "Description" .textInput
    | .quantity => .field "Quantity" .naturalInput
    | .unitPrice => .field "Unit price (cents)" .naturalInput

def form : Form invoice invoice := .list "Invoice" itemForm newItem

end Forms.ExampleForms.Invoice
