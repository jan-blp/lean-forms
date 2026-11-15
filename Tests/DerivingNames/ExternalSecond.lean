module

public import Forms.Model.Derive

@[expose] public section
open Forms.Model
namespace Tests.DerivingNames.Models

structure ExternalSecond where
  value : Nat

end Tests.DerivingNames.Models

namespace Tests.DerivingNames.Shared

deriving instance FormModel for Models.ExternalSecond

end Tests.DerivingNames.Shared
