module

public import Forms.Model.Derive

@[expose] public section
open Forms.Model
namespace Tests.DerivingNames.Shared

inductive SumFirst where
  | a (value : Nat)
  | b
  deriving FormModel

end Tests.DerivingNames.Shared
