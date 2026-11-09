module

public import Lean.Data.Json
public import FormsReact.Component

@[expose] public section
namespace Forms.Runtime.Wire
open Lean

inductive Event where
  | apply (key : String) (argument : Json)
  | submit
  | reset
  | complete (status : Nat) (body : String)
  | failed (message : String)
  deriving ToJson, FromJson

inductive Command where
  | event (message : Event)
  | apply (key : String) (argument : Json)
  | reset
  | validate
  | inspect
  | serverError (status : Nat) (body : String)
  deriving ToJson, FromJson

structure CompiledDescriptor where
  form : String
  fingerprint : String
  value : Json
  deriving ToJson, FromJson

inductive Request where
  | open (descriptor : CompiledDescriptor)
  | send (handle : String) (request : Command)
  | dispose (handle : String)
  deriving ToJson, FromJson

inductive HttpMethod where
  | POST
  deriving ToJson, FromJson

structure HttpHeaders where
  «Content-Type» : String
  deriving ToJson, FromJson

structure HttpEffect where
  url : String
  method : HttpMethod
  headers : HttpHeaders
  body : String
  deriving ToJson, FromJson

/-- Browser-facing snapshot returned after opening or updating a form. -/
structure Snapshot where
  title : String
  view : FormsReact.Component
  /-- Why the last `apply` event was rejected. -/
  rejection : Option String
  effects : List HttpEffect
  summary : String
  submissionBlocked : Bool
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
