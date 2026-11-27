module

public import Forms.Model.Basic
public import Std.Data.HashMap
public import Mathlib.Data.FinEnum

@[expose] public section
namespace Forms.Model
open Lean

inductive HttpMethod where
  | get
  | post
  deriving BEq, Hashable, Repr, ToJson, FromJson

structure HttpRequest where
  method : HttpMethod
  url : String
  body : Option String
  deriving BEq, Hashable, Repr, ToJson, FromJson

inductive RequestScope where
  | request (request : HttpRequest)
  | endpoint (method : HttpMethod) (url : String)
  deriving BEq, Repr

def RequestScope.contains (scope : RequestScope) (request : HttpRequest) : Bool :=
  match scope with
  | .request target => target == request
  | .endpoint method url => request.method == method && request.url == url

structure HttpFetch where
  request : HttpRequest
  generation : Nat
  deriving BEq, Repr, ToJson, FromJson

structure HttpCall where
  id : Uuid
  request : HttpRequest
  deriving BEq

inductive Source (α : Type) where
  | pure (value : α)
  | fetch (request : HttpRequest) (decode : Json → Except String α)

def Source.request? {α : Type} : Source α → Option HttpRequest
  | .pure _ => none
  | .fetch request _ => some request

inductive HttpRequest.Response where
  | loading (generation : Nat)
  | loaded (response : Json)
  | failed (message : String)

abbrev HttpRequest.Cache := Std.HashMap HttpRequest HttpRequest.Response

inductive Status (α : Type) where
  | loading
  | ready (value : α)
  | failed (message : String)
  deriving DecidableEq

def Source.resolve {α : Type} (cache : HttpRequest.Cache) : Source α → Status α
  | .pure value => .ready value
  | .fetch request decode =>
    match cache[request]? with
    | none => .loading
    | some (.loading _) => .loading
    | some (.failed message) => .failed message
    | some (.loaded response) =>
      match decode response with
      | .ok value => .ready value
      | .error message => .failed message

-- This is needed so that the desired ToJson instance for Unit takes precedence.
attribute [instance high] instToJsonUnit instFromJsonUnit

structure Api.Signature where
  Input : Type
  Output : Type
  [inputToJson : ToJson Input]
  [inputFromJson : FromJson Input]
  [outputToJson : ToJson Output]
  [outputFromJson : FromJson Output]

attribute [instance]
  Api.Signature.inputToJson
  Api.Signature.inputFromJson
  Api.Signature.outputToJson
  Api.Signature.outputFromJson

/-- Calls POST the signature's JSON input to the endpoint's `path` and decode its output. -/
class Api (endpoint : Type) [FinEnum endpoint] where
  signature : endpoint → Api.Signature
  path : endpoint → String
  distinct : FinEnum.toList endpoint |>.map path |>.Nodup

def Api.method : HttpMethod := .post

structure Api.Call (endpoint : Type) [FinEnum endpoint] [Api endpoint] where
  named : endpoint
  input : (Api.signature named).Input

def Api.request
  {endpoint : Type}
  [FinEnum endpoint]
  [Api endpoint]
  (named : endpoint)
  (input : (Api.signature named).Input)
  : HttpRequest :=
  { method := Api.method, url := Api.path named, body := some (toJson input).compress }

def Api.source
  {endpoint : Type}
  [FinEnum endpoint]
  [Api endpoint]
  (named : endpoint)
  (input : (Api.signature named).Input)
  : Source (Api.signature named).Output :=
  .fetch (Api.request named input) fromJson?

def Api.scope
  {endpoint : Type}
  [FinEnum endpoint]
  [Api endpoint]
  (named : endpoint)
  : RequestScope :=
  .endpoint Api.method (Api.path named)

def Api.parse
  {endpoint : Type}
  [FinEnum endpoint]
  [Api endpoint]
  (request : HttpRequest)
  : Option (Api.Call endpoint) := do
  guard (request.method == Api.method)
  let named ← (FinEnum.toList endpoint).find? (Api.path · == request.url)
  let input ← (Json.parse (request.body.getD "") >>= fromJson?).toOption
  return ⟨named, input⟩

def Api.serve
  {endpoint : Type}
  [FinEnum endpoint]
  [Api endpoint]
  (handle : (named : endpoint) → (Api.signature named).Input → Option (Api.signature named).Output)
  (request : HttpRequest)
  : Option Json := do
  let call ← Api.parse (endpoint := endpoint) request
  let output ← handle call.named call.input
  return toJson output

end Forms.Model
