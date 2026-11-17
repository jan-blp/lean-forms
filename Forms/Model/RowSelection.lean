module

public import Forms.Model.Scalar

@[expose] public section
namespace Forms.Model

inductive RowSelection where
  | none
  | row (id : Uuid)
  deriving BEq, DecidableEq, Repr

end Forms.Model
