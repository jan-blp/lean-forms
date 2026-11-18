module

public import Forms.Model.ErasedLocation
public import Std.Data.HashMap
public import Lean.Data.Json

@[expose] public section
namespace Forms.Model

namespace Diagnostic

inductive ReportState where
  | unresolved
  | resolved
  deriving BEq, DecidableEq, Repr, Lean.ToJson, Lean.FromJson

inductive Severity where
  | warning
  | info
  deriving BEq, DecidableEq, Repr, Lean.ToJson, Lean.FromJson

structure ReportKind where
  state : ReportState
  severity : Severity
  /-- Reads server data older than the current value. -/
  outdated : Bool
  deriving BEq, DecidableEq, Repr, Lean.ToJson, Lean.FromJson

inductive Kind where
  | error
  /-- Never blocks submit. -/
  | report (kind : ReportKind)
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

def Message.errors (messages : List Message) : List String :=
  (messages.filter (·.kind == .error)).map (·.text)

/-- A report's message as shown at one of its locations. -/
structure ReportMessage where
  kind : Diagnostic.ReportKind
  text : String
  deriving BEq, DecidableEq, Repr

def Message.reports (messages : List Message) : List ReportMessage :=
  messages.filterMap fun message => match message.kind with
    | .error => none
    | .report kind => some { kind, text := message.text }

/-- Listed by the `issues` node. -/
def Diagnostic.Kind.actionable : Diagnostic.Kind → Bool
  | .error => true
  | .report kind => kind.severity == .warning && kind.state == .unresolved

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
  (diagnostics.filter (·.kind.actionable)).filterMap fun diagnostic => match diagnostic.targets with
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
