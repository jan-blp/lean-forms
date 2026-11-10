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

/-- Typed HTTP endpoints: a call to `named` sends an `Input named` and returns an `Output named`.
Calls are POSTs of the JSON input to the endpoint's `path`. -/
class Api (endpoint : Type) where
  Input : endpoint → Type
  Output : endpoint → Type
  path : endpoint → String
  all : List endpoint
  complete : ∀ named, named ∈ all
  distinct : (all.map path).Nodup
  inputToJson : (named : endpoint) → ToJson (Input named)
  inputFromJson : (named : endpoint) → FromJson (Input named)
  outputToJson : (named : endpoint) → ToJson (Output named)
  outputFromJson : (named : endpoint) → FromJson (Output named)

/-- An endpoint and its input. -/
structure Api.Call (endpoint : Type) [Api endpoint] where
  named : endpoint
  input : Api.Input named

def Api.request
  {endpoint : Type}
  [Api endpoint]
  (named : endpoint)
  (input : Api.Input named)
  : HttpRequest :=
  letI := Api.inputToJson named
  { method := .post, url := Api.path named, body := some (toJson input).compress }

def Api.source
  {endpoint : Type}
  [Api endpoint]
  (named : endpoint)
  (input : Api.Input named)
  : Source (Api.Output named) :=
  letI := Api.outputFromJson named
  .fetch (Api.request named input) fromJson?

/-- The call `request` names. -/
def Api.parse
  {endpoint : Type}
  [Api endpoint]
  (request : HttpRequest)
  : Option (Api.Call endpoint) := do
  guard (request.method == .post)
  let named ← (Api.all : List endpoint).find? (Api.path · == request.url)
  let decode := (Api.inputFromJson named).fromJson?
  let input ← (Json.parse (request.body.getD "") >>= decode).toOption
  return ⟨named, input⟩

/-- The encoded response `handle` gives to `request`. -/
def Api.serve
  {endpoint : Type}
  [Api endpoint]
  (handle : (named : endpoint) → Api.Input named → Option (Api.Output named))
  (request : HttpRequest)
  : Option Json := do
  let call ← Api.parse (endpoint := endpoint) request
  let output ← handle call.named call.input
  return (Api.outputToJson call.named).toJson output

structure KeyedOption (key : Type) where
  key : key
  label : String
  deriving ToJson, FromJson

@[reducible] instance : FormModel Unit := ⟨Unit, id⟩
instance : Validation Unit := ⟨fun value => .ok ⟨value, rfl⟩⟩

/-- Selects `picked`, stashing the current payload; a key picked before gets its payload back. -/
def Selection.pick
  {key payload : Type}
  [BEq key]
  [Hashable key]
  (picked : key)
  (initial : payload)
  (selection : Selection key payload)
  : Selection key payload :=
  if selection.selected.any (·.1 == picked) then selection else
  let known := match selection.selected with
    | some (current, payload) => selection.stash.insert current payload
    | none => selection.stash
  { selected := some (picked, known.getD picked initial)
    stash := known.erase picked }

/-- Only the selection is encoded; stashed payloads stay with the open form. -/
instance
    {key payload : Type}
    [BEq key]
    [Hashable key]
    [ToJson key]
    [ToJson payload]
    : ToJson (Selection key payload) where
  toJson selection := match selection.selected with
    | none => .null
    | some (key, payload) => Json.mkObj [("key", toJson key), ("payload", toJson payload)]

instance
    {key payload : Type}
    [BEq key]
    [Hashable key]
    [FromJson key]
    [FromJson payload]
    : FromJson (Selection key payload) where
  fromJson? json :=
    if json.isNull then pure .empty else do
      let key ← fromJson? (← json.getObjVal? "key")
      let payload ← fromJson? (← json.getObjVal? "payload")
      pure { selected := some (key, payload), stash := {} }

/-- A validated selection; stashed payloads stay raw. -/
structure Selected (key model : Type) [BEq key] [Hashable key] [FormModel model] where
  selected : Option (key × model)
  stash : Std.HashMap key (FormModel.Raw model)

@[reducible] instance
    {key model : Type}
    [BEq key]
    [Hashable key]
    [FormModel model]
    : FormModel (Selected key model) where
  Raw := Selection key (FormModel.Raw model)
  erase selection :=
    { selected := selection.selected.map fun (key, value) => (key, FormModel.erase value)
      stash := selection.stash }

/-- Validates the selected payload; errors point into it. -/
instance
    {key model : Type}
    [BEq key]
    [Hashable key]
    [FormModel model]
    [Validation model]
    : Validation (Selected key model) where
  validate
    | ⟨none, stash⟩ => .ok ⟨⟨none, stash⟩, rfl⟩
    | ⟨some (key, payload), stash⟩ =>
      match Validation.validate (model := model) payload with
      | .ok ⟨value, erased⟩ => .ok ⟨⟨some (key, value), stash⟩, by subst erased; rfl⟩
      | .error errors => .error (errors.map (Error.mapLocations (.selected key stash)))

/-- `value` next to a read-only `context`: loaded data, or the picked key.
`value` has an empty key, so it adds no step to locations. -/
structure Scope (context value : Type) where
  context : context
  value : value

inductive Scope.Field (context value : Type) : Type → Type where
  | context : Field context value context
  | value : Field context value value

def Scope.Field.key {context value α : Type} : Field context value α → String
  | .context => "context"
  | .value => ""

def Scope.Field.lens
  {context value α : Type}
  : Field context value α → LeanLens.Lens' (Scope context value) α
  | .context => LeanLens.mkLens (·.context) fun new scope => { scope with context := new }
  | .value => LeanLens.mkLens (·.value) fun new scope => { scope with value := new }

instance Scope.Field.lawful
  {context value α : Type}
  (field : Field context value α)
  : LeanLens.LawfulLens field.lens := by
  cases field <;> constructor <;> intros <;> rfl

@[reducible] instance {context value : Type} : Fields (Scope context value) where
  Field := Scope.Field context value
  lens := Scope.Field.lens
  lawful := Scope.Field.lawful
  key := Scope.Field.key
  key_injective := by
    intro α β a b h
    cases a <;> cases b <;> simp_all [Scope.Field.key]

end Forms.Model
