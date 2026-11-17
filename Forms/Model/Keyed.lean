module

public import Forms.Model.Scalar

@[expose] public section
namespace Forms.Model

/-- Collection items, addressed by an id that survives insertions and removals. -/
class Keyed (β : Type) where
  id : β → Uuid

end Forms.Model
