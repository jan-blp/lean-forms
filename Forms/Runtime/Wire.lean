module

public import Lean.Data.Json
public import Forms.Runtime.DisplayLayout

@[expose] public section
namespace Forms.Runtime.Wire
open Lean

deriving instance ToJson, FromJson for DisplayLayout.Tag

inductive DomArgument where
  | none | value | checked
  deriving ToJson, FromJson

inductive BindingCommand where
  | apply | draft | submit | reset
  deriving ToJson, FromJson

inductive DomEvent where
  | click | input | change | submit
  deriving ToJson, FromJson

structure Binding where
  event : DomEvent
  command : BindingCommand
  key : String
  source : String
  argument : DomArgument
  deriving ToJson, FromJson

inductive DisplayView where
  | element (tag : DisplayLayout.Tag) (attributes : List (String × String))
      (children : List (Option DisplayView)) (bindings : List Binding)
      (text : Option String) (value : Option String) (checked : Option Bool) (focusKey : Option String)
  deriving ToJson, FromJson

inductive FormEvent where
  | apply (key : String) (argument : Json)
  | draft (key argument : String)
  | submit | reset
  | complete (status : Nat) (body : String)
  | failed (message : String)
  deriving ToJson, FromJson

inductive FormRequest where
  | event (message : FormEvent)
  | apply (key : String) (argument : Json)
  | reset | validate | inspect
  | serverError (status : Nat) (body : String)
  deriving ToJson, FromJson

structure CompiledDescriptor where
  form : String
  revision : String
  value : Json
  deriving ToJson, FromJson

inductive Request where
  | open (descriptor : CompiledDescriptor)
  | send (handle : String) (request : FormRequest)
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

/-- Browser-facing snapshot returned after opening or updating a form.
Contains the display, feedback, submission payload, and HTTP effects for the
browser to perform. -/
structure Snapshot where
  title : String
  view : Option DisplayView
  render : Bool
  focus : Option String
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
