module

public import Forms.Model.Derive

@[expose] public section
open Forms.Model
namespace Tests.DerivingNames.Shared

inductive SumSecond where
  | a (value : String)
  | b
  deriving FormModel

end Tests.DerivingNames.Shared
