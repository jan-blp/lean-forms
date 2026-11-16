module

public import Forms.Model.ErasedLocation

@[expose] public section

namespace Forms.Runtime.Feedback
open Forms.Model (ErasedLocation)

inductive Targets where
  | global
  | locations (first : ErasedLocation) (rest : List ErasedLocation)

structure Error where
  message : String
  targets : Targets

structure ServerError where
  message : String
  errors : List Error := []

def summary (errors : List Error) : String :=
  String.intercalate "\n" (errors.map (·.message))

def messages (errors : List Error) (path : ErasedLocation) : Option String :=
  let matched := (errors.filterMap fun error =>
    match error.targets with
    | .locations first rest => if (first :: rest).contains path then some error.message else none
    | _ => none).eraseDups
  if matched.isEmpty then none else some (String.intercalate "\n" matched)

end Forms.Runtime.Feedback
