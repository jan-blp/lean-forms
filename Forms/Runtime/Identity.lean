module

@[expose] public section

namespace Forms.Runtime

structure ControlKey where
  value : String
  deriving DecidableEq

structure DomId where
  value : String
  deriving BEq, DecidableEq

end Forms.Runtime
