module



@[expose] public section

namespace Forms.Runtime.Feedback

/-- Display locations retain field and constructor identity independently of JSON. -/
inductive Step where
  | field (name : String)
  | constructor (tag : String)
  deriving BEq, DecidableEq

abbrev Location := List Step

inductive Targets where
  | global
  | locations (first : Location) (rest : List Location)

structure Error where
  message : String
  targets : Targets

structure ServerError where
  message : String
  errors : List Error := []

def summary (errors : List Error) : String :=
  String.intercalate "\n" (errors.map (·.message))

/-- Messages are matched and deduplicated before the view is serialized. -/
def messages (errors : List Error) (path : Location) : Option String :=
  let matched := (errors.filterMap fun error =>
    match error.targets with
    | .locations first rest => if (first :: rest).contains path then some error.message else none
    | _ => none).eraseDups
  if matched.isEmpty then none else some (String.intercalate "\n" matched)

end Forms.Runtime.Feedback
