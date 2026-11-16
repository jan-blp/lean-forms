module

@[expose] public section
namespace Forms.Model

namespace ErasedLocation

inductive Step where
  | field (name : String)
  | constructor (tag : String)
  | index (position : Nat)
  deriving BEq, DecidableEq

end ErasedLocation

/-- A location with its types erased -/
abbrev ErasedLocation := List ErasedLocation.Step

end Forms.Model
