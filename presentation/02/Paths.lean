-- The nested-path diagram, checked from "add records and groups" onward:
-- lake env lean -DwarningAsError=true /path/to/presentation/02/Paths.lean
import Forms.Core.Path

namespace Forms.Presentation.Paths

inductive AddressField where
  | street | city
  deriving DecidableEq, Repr
instance : FinEnum AddressField :=
  FinEnum.ofList [.street, .city] (by grind [AddressField])
def addressFields : Enum where
  type := AddressField
  label | .street => "street" | .city => "city"
abbrev address : DataType := .record addressFields fun
  | .street => .text
  | .city => .text

inductive CustomerField where
  | address | name
  deriving DecidableEq, Repr
instance : FinEnum CustomerField :=
  FinEnum.ofList [.address, .name] (by grind [CustomerField])
def customerFields : Enum where
  type := CustomerField
  label | .address => "address" | .name => "name"
abbrev customer : DataType := .record customerFields fun
  | .address => address
  | .name => .text

inductive OrderField where
  | customer | number
  deriving DecidableEq, Repr
instance : FinEnum OrderField :=
  FinEnum.ofList [.customer, .number] (by grind [OrderField])
def orderFields : Enum where
  type := OrderField
  label | .customer => "customer" | .number => "number"
abbrev order : DataType := .record orderFields fun
  | .customer => customer
  | .number => .natural

def streetPath : Path order .text :=
  .field .customer (.field .address (.field .street .self))

def initial : ⟦order⟧
  | .customer => fun
    | .address => fun | .street => "Lambda Lane" | .city => "Paris"
    | .name => "Ada"
  | .number => 42

#guard Path.get streetPath initial == "Lambda Lane"
#guard Path.get streetPath (Path.set streetPath "New Street" initial) == "New Street"
#guard (Path.set streetPath "New Street" initial) .number == 42

end Forms.Presentation.Paths
