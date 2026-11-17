module

public import Forms.Model.Scalar

@[expose] public section
namespace Forms.Model

class HasUuid (β : Type) where
  id : β → Uuid

end Forms.Model
