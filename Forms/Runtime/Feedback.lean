module

public import Forms.Core.Validation

@[expose] public section

namespace Forms.Runtime.Feedback

/-- Display locations retain field, item, and constructor identity independently of JSON. -/
inductive Step where
  | field (name : String)
  | item (index : Nat)
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

def location {ty : DataType} : Validation.Location ty → Location
  | .self => []
  | .field (fieldNames := names) name rest => .field (names.label name) :: location rest
  | .item index rest => .item index :: location rest
  | .constructor (tags := tags) tag rest => .constructor (tags.label tag) :: location rest

def ofResolved {ty : DataType} (error : Validation.ResolvedError ty) : Error :=
  { message := error.message
    targets := match error.targets with
      | .global => .global
      | .locations (first :: rest) _ => .locations (location first) (rest.map location) }

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
