module

public import Forms.Model.ErasedLocation
public import Std.Data.HashMap

@[expose] public section
namespace Forms.Model

namespace Diagnostic

inductive Targets where
  | global
  | locations (first : ErasedLocation) (rest : List ErasedLocation)
  deriving BEq, DecidableEq

end Diagnostic

structure Diagnostic where
  message : String
  targets : Diagnostic.Targets
  deriving BEq, DecidableEq

/-- Valid for one evaluation revision; locations remain absolute across model focus. -/
structure Destination where
  locations : List ErasedLocation
  revision : Nat
  deriving BEq, DecidableEq

structure Issue where
  message : String
  destination? : Option Destination
  deriving BEq, DecidableEq

def Diagnostic.locations (diagnostic : Diagnostic) : List ErasedLocation :=
  match diagnostic.targets with
  | .global => []
  | .locations first rest => first :: rest

def Diagnostic.issues
  (diagnostics : List Diagnostic)
  (scope : ErasedLocation)
  (revision : Nat)
  : List Issue :=
  diagnostics.filterMap fun diagnostic => match diagnostic.targets with
    | .global =>
      if scope.isEmpty then some { message := diagnostic.message, destination? := none } else none
    | .locations first rest =>
      let locations := (first :: rest).filter (scope.isPrefixOf ·)
      if locations.isEmpty then none
      else some { message := diagnostic.message, destination? := some { locations, revision } }

def Diagnostic.summary (diagnostics : List Diagnostic) : String :=
  String.intercalate "\n" (diagnostics.map (·.message))

/-- Each location's distinct messages, in diagnostic order. -/
def Diagnostic.messageIndex
  (diagnostics : List Diagnostic)
  : Std.HashMap ErasedLocation (List String) :=
  diagnostics.foldl (init := {}) fun index diagnostic => match diagnostic.targets with
    | .global => index
    | .locations first rest =>
      (first :: rest).foldl (init := index) fun index location =>
        let messages := index.getD location []
        if messages.contains diagnostic.message then index
        else index.insert location (messages ++ [diagnostic.message])

end Forms.Model
