module

public import Forms.Runtime.Feedback
public import Lean.Data.Json
public import Forms.Model.Format

@[expose] public section

namespace Forms.Runtime.FeedbackProtocol
open Lean Feedback
open Forms.Model (ErasedLocation Uuid)

def locationToJson (location : ErasedLocation) : Json :=
  toJson (location.map fun step => match step with
    | .field name => Json.mkObj [("kind", toJson "field"), ("name", toJson name)]
    | .constructor tag => Json.mkObj [("kind", toJson "constructor"), ("tag", toJson tag)]
    | .item id => Json.mkObj [("kind", toJson "item"), ("id", toJson id)])

def locationFromJson (json : Json) : Except String ErasedLocation := do
  (← json.getArr?).toList.mapM fun step => do
    match ← step.getObjValAs? String "kind" with
    | "field" => pure (.field (← step.getObjValAs? String "name"))
    | "constructor" => pure (.constructor (← step.getObjValAs? String "tag"))
    | "item" => pure (.item (← step.getObjValAs? Uuid "id"))
    | _ => throw "Invalid location step"

def targetsToJson : Model.Diagnostic.Targets → Json
  | .global => Json.mkObj [("kind", toJson "global")]
  | .locations first rest => Json.mkObj [("kind", toJson "locations"),
      ("locations", toJson ((first :: rest).map locationToJson))]

def targetsFromJson (json : Json) : Except String Model.Diagnostic.Targets := do
  match ← json.getObjValAs? String "kind" with
  | "global" => pure .global
  | "locations" => do
    let locations ← (← (← json.getObjVal? "locations").getArr?).toList.mapM locationFromJson
    let first :: rest := locations | throw "Empty locations"
    pure (.locations first rest)
  | _ => throw "Invalid validation target"

instance : ToJson Model.Diagnostic.Targets := ⟨targetsToJson⟩
instance : FromJson Model.Diagnostic.Targets := ⟨targetsFromJson⟩

deriving instance ToJson, FromJson for ValidationError, ServerError

def errorToJson (error : Model.Diagnostic) : Json :=
  toJson ({ message := error.message, targets := error.targets } : ValidationError)

/-- Decode once at the boundary; malformed responses never partially accept errors. -/
def serverError? (body : String) : Option ServerError :=
  match Json.parse body >>= fromJson? (α := ServerError) with
  | .ok error => if error.message.isEmpty then none else some error
  | .error _ => none

end Forms.Runtime.FeedbackProtocol
