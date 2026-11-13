module

public import Lean.Data.Json
public import FormsReact.Component

@[expose] public section
namespace Forms.Runtime.Wire
open Lean

inductive HttpOutcome where
  | response (status : Nat) (body : String)
  | unreachable (message : String)
  deriving ToJson, FromJson

inductive Event where
  | apply (key : String) (argument : Json)
  | submit
  | reset
  /-- The outcome of the `submit` effect. -/
  | submitted (outcome : HttpOutcome)
  /-- The outcome of the `fetch` effect with `id`. -/
  | fetched (id : String) (outcome : HttpOutcome)
  deriving ToJson, FromJson

/-- What opening a form needs: its registered name, its code version, and its starting value. -/
structure FormStart where
  form : String
  fingerprint : String
  value : Json
  deriving ToJson, FromJson

inductive Request where
  | open (start : FormStart)
  | send (handle : String) (event : Event)
  | dispose (handle : String)
  deriving ToJson, FromJson

inductive HttpMethod where
  | GET
  | POST
  deriving ToJson, FromJson

structure HttpHeaders where
  «Content-Type» : String
  deriving ToJson, FromJson

structure HttpEffect where
  url : String
  method : HttpMethod
  headers : HttpHeaders
  body : Option String
  deriving ToJson, FromJson

/-- A request for the browser to send. -/
inductive Effect where
  /-- Answered by `submitted`. -/
  | submit (request : HttpEffect)
  /-- Answered by `fetched` with `id`. -/
  | fetch (id : String) (request : HttpEffect)
  deriving ToJson, FromJson

/-- Browser-facing snapshot returned after opening or updating a form. -/
structure Snapshot where
  title : String
  view : FormsReact.Component
  /-- Why the last `apply` event was rejected. -/
  rejection : Option String
  /-- Names of the fields whose drafts React keeps. -/
  draftFields : List String
  effects : List Effect
  controls : List Json
  submission : Json
  errors : List Json
  deriving ToJson, FromJson

inductive Response where
  | opened (handle : String) (snapshot : Snapshot)
  | updated (snapshot : Snapshot)
  | disposed
  deriving ToJson, FromJson

structure Success where
  ok : Bool
  value : Response
  deriving ToJson, FromJson

structure Failure where
  ok : Bool
  error : String
  deriving ToJson, FromJson

end Forms.Runtime.Wire
