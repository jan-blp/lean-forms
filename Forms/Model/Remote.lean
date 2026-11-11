module

public import Forms.Model.Basic
public import Std.Data.HashMap

@[expose] public section
namespace Forms.Model
open Lean

inductive HttpMethod where
  | get
  | post
  deriving BEq, Hashable, Repr, ToJson, FromJson

/-- A request whose JSON response a form can load. -/
structure HttpRequest where
  method : HttpMethod
  url : String
  body : Option String
  deriving BEq, Hashable, Repr, ToJson, FromJson

inductive Source (α : Type) where
  | pure (value : α)
  | fetch (request : HttpRequest) (decode : Json → Except String α)

def Source.request? {α : Type} : Source α → Option HttpRequest
  | .pure _ => none
  | .fetch request _ => some request

inductive HttpRequest.Response where
  | loading
  | loaded (response : Json)
  | failed (message : String)

abbrev HttpRequest.Cache := Std.HashMap HttpRequest HttpRequest.Response

inductive Status (α : Type) where
  | loading
  | ready (value : α)
  | failed (message : String)

def Source.resolve {α : Type} (cache : HttpRequest.Cache) : Source α → Status α
  | .pure value => .ready value
  | .fetch request decode =>
    match cache[request]? with
    | none => .loading
    | some .loading => .loading
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

/-- Typed HTTP endpoints: a call to `named` sends its signature's `Input` and returns its `Output`.
Calls are POSTs of the JSON input to the endpoint's `path`. -/
class Api (endpoint : Type) where
  signature : endpoint → Api.Signature
  path : endpoint → String
  all : List endpoint
  complete : ∀ named, named ∈ all
  distinct : (all.map path).Nodup

/-- An endpoint and its input. -/
structure Api.Call (endpoint : Type) [Api endpoint] where
  named : endpoint
  input : (Api.signature named).Input

def Api.request
  {endpoint : Type}
  [Api endpoint]
  (named : endpoint)
  (input : (Api.signature named).Input)
  : HttpRequest :=
  { method := .post, url := Api.path named, body := some (toJson input).compress }

def Api.source
  {endpoint : Type}
  [Api endpoint]
  (named : endpoint)
  (input : (Api.signature named).Input)
  : Source (Api.signature named).Output :=
  .fetch (Api.request named input) fromJson?

/-- The call `request` names. -/
def Api.parse
  {endpoint : Type}
  [Api endpoint]
  (request : HttpRequest)
  : Option (Api.Call endpoint) := do
  guard (request.method == .post)
  let named ← (Api.all : List endpoint).find? (Api.path · == request.url)
  let input ← (Json.parse (request.body.getD "") >>= fromJson?).toOption
  return ⟨named, input⟩

/-- The encoded response `handle` gives to `request`. -/
def Api.serve
  {endpoint : Type}
  [Api endpoint]
  (handle : (named : endpoint) → (Api.signature named).Input → Option (Api.signature named).Output)
  (request : HttpRequest)
  : Option Json := do
  let call ← Api.parse (endpoint := endpoint) request
  let output ← handle call.named call.input
  return toJson output

end Forms.Model
