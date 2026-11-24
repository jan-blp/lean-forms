module

public import Forms.Model.Collection

@[expose] public section
namespace Forms.Model

inductive RowSelection where
  | none
  | row (id : Uuid)
  deriving BEq, DecidableEq, Repr

def RowSelection.of {β : Type} (entry : Item β) : RowSelection :=
  .row entry.id

end Forms.Model
