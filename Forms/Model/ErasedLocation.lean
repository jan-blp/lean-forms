module

@[expose] public section
namespace Forms.Model

namespace ErasedLocation

inductive Step where
  | field (name : String)
  | constructor (tag : String)
  -- TODO: use a stable item id. Positions shift on insertion and deletion, which is why
  -- destinations need revisions and `invalidatesDestinations`.
  | index (position : Nat)
  deriving BEq, DecidableEq, Hashable

end ErasedLocation

/-- A location with its types erased -/
abbrev ErasedLocation := List ErasedLocation.Step

end Forms.Model
