module

public import Forms.Model.Scalar

@[expose] public section
namespace Forms.Model

namespace ErasedLocation

inductive Step where
  | field (name : String)
  | constructor (tag : String)
  | item (id : Uuid)
  deriving BEq, DecidableEq, Hashable

end ErasedLocation

/-- A location with its types erased -/
abbrev ErasedLocation := List ErasedLocation.Step

end Forms.Model
