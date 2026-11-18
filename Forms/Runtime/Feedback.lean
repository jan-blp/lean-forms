module

public import Forms.Model.Diagnostic

@[expose] public section

namespace Forms.Runtime.Feedback

structure ValidationError where
  message : String
  targets : Model.Diagnostic.Targets
  deriving BEq

def ValidationError.diagnostic (error : ValidationError) : Model.Diagnostic :=
  { kind := .error, message := error.message, targets := error.targets }

inductive ServerError where
  /-- About the submission as a whole, such as a stale form. -/
  | invalidRequest (message : String)
  | validation (first : ValidationError) (rest : List ValidationError)

def ServerError.errors : ServerError → List Model.Diagnostic
  | .invalidRequest _ => []
  | .validation first rest => (first :: rest).map (·.diagnostic)

def ServerError.message (error : ServerError) : String :=
  match error with
  | .invalidRequest message => message
  | .validation .. => Model.Diagnostic.summary error.errors

end Forms.Runtime.Feedback
