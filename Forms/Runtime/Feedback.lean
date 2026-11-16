module

public import Forms.Model.Diagnostic

@[expose] public section

namespace Forms.Runtime.Feedback

structure ServerError where
  message : String
  errors : List Model.Diagnostic := []

end Forms.Runtime.Feedback
