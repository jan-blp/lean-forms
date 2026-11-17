module

public import Forms.Model.HasUuid

@[expose] public section
namespace Forms.Model

inductive RowSelection where
  | none
  | row (id : Uuid)
  deriving BEq, DecidableEq, Repr

def RowSelection.of {β : Type} [HasUuid β] (item : β) : RowSelection :=
  .row (HasUuid.id item)

end Forms.Model
