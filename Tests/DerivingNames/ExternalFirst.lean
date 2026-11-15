module

public import Forms.Model.Derive

@[expose] public section
open Forms.Model
namespace Tests.DerivingNames.Models

structure ExternalFirst where
  value : String

end Tests.DerivingNames.Models

namespace Tests.DerivingNames.Shared

deriving instance FormModel for Models.ExternalFirst

end Tests.DerivingNames.Shared
