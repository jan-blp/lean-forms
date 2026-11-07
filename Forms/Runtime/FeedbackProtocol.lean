module

public import Forms.Runtime.Feedback
public import Lean

@[expose] public section

namespace Forms.Runtime.FeedbackProtocol
open Lean Feedback

def locationToJson (location : Location) : Json :=
  toJson (location.map fun step => match step with
    | .field name => Json.mkObj [("kind", toJson "field"), ("name", toJson name)]
    | .item index => Json.mkObj [("kind", toJson "item"), ("index", toJson (toString index))]
    | .constructor tag => Json.mkObj [("kind", toJson "constructor"), ("tag", toJson tag)])

def locationFromJson (json : Json) : Except String Location := do
  (← json.getArr?).toList.mapM fun step => do
    match ← step.getObjValAs? String "kind" with
    | "field" => pure (.field (← step.getObjValAs? String "name"))
    | "constructor" => pure (.constructor (← step.getObjValAs? String "tag"))
    | "item" =>
      let text ← step.getObjValAs? String "index"
      if text.isEmpty || !text.toList.all (fun c => '0' ≤ c && c ≤ '9') then throw "Invalid item index"
      let some index := text.toNat? | throw "Invalid item index"
      pure (.item index)
    | _ => throw "Invalid location step"

def errorFromJson (json : Json) : Except String Error := do
  let message ← json.getObjValAs? String "message"
  let targets ← json.getObjVal? "targets"
  let targets ← match ← targets.getObjValAs? String "kind" with
    | "global" => pure Targets.global
    | "invalidTarget" => pure (.invalidTarget (← locationFromJson (← targets.getObjVal? "location")))
    | "locations" => do
      let locations ← (← (← targets.getObjVal? "locations").getArr?).toList.mapM locationFromJson
      let first :: rest := locations | throw "Empty locations"
      pure (.locations first rest)
    | _ => throw "Invalid validation target"
  pure { message, targets }

/-- Decode once at the boundary; malformed responses never partially accept errors. -/
def serverError (status : Nat) (body : String) : ServerError :=
  let parsed : Except String ServerError := do
    let error ← (← Json.parse body).getObjVal? "error"
    let message ← error.getObjValAs? String "message"
    if message.isEmpty then throw "Empty message"
    match ← error.getObjValAs? String "kind" with
    | "request" | "replay" => pure { message }
    | "validation" => pure { message, errors := ← (← (← error.getObjVal? "errors").getArr?).toList.mapM errorFromJson }
    | _ => throw "Unknown error kind"
  parsed.toOption.getD { message := s!"Submission failed (HTTP {status})." }

end Forms.Runtime.FeedbackProtocol
