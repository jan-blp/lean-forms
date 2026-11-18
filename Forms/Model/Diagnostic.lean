module

public import Forms.Model.ErasedLocation
public import Std.Data.HashMap
public import Lean.Data.Json

@[expose] public section
namespace Forms.Model

namespace Diagnostic

inductive Kind where
  | error
  /-- Never blocks submit, such as a failing server check. -/
  | report
  deriving BEq, DecidableEq, Lean.ToJson, Lean.FromJson

inductive Targets where
  | global
  | locations (first : ErasedLocation) (rest : List ErasedLocation)
  deriving BEq, DecidableEq

end Diagnostic

structure Diagnostic where
  kind : Diagnostic.Kind
  message : String
  targets : Diagnostic.Targets
  deriving BEq, DecidableEq

/-- A diagnostic's message as shown at one of its locations. -/
structure Message where
  kind : Diagnostic.Kind
  text : String
  deriving BEq, DecidableEq

def Message.texts (kind : Diagnostic.Kind) (messages : List Message) : List String :=
  (messages.filter (·.kind == kind)).map (·.text)

structure Destination where
  locations : List ErasedLocation
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
  : List Issue :=
  diagnostics.filterMap fun diagnostic => match diagnostic.targets with
    | .global =>
      if scope.isEmpty then some { message := diagnostic.message, destination? := none } else none
    | .locations first rest =>
      let locations := (first :: rest).filter (scope.isPrefixOf ·)
      if locations.isEmpty then none
      else some { message := diagnostic.message, destination? := some { locations } }

def Diagnostic.summary (diagnostics : List Diagnostic) : String :=
  String.intercalate "\n" (diagnostics.map (·.message))

/-- Each location's distinct messages, in diagnostic order. -/
def Diagnostic.messageIndex
  (diagnostics : List Diagnostic)
  : Std.HashMap ErasedLocation (List Message) :=
  diagnostics.foldl (init := {}) fun index diagnostic =>
    let message := { kind := diagnostic.kind, text := diagnostic.message }
    diagnostic.locations.foldl (init := index) fun index location =>
      let messages := index.getD location []
      if messages.contains message then index
      else index.insert location (messages ++ [message])

end Forms.Model
