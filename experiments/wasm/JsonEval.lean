module

public import Forms.Runtime.ValidationProtocol
public import Forms.Runtime.InputProtocol

public section

namespace WasmExperiment
open Lean Forms.Runtime

private def encodeResponse (result : Except String (List (String × Json))) : String :=
  (match result with
    | .ok fields => Json.mkObj (("ok", toJson true) :: fields)
    | .error error => Json.mkObj [("ok", toJson false), ("error", toJson error)]).compress

/-- A single transport boundary: parse, decode, evaluate, then serialize. -/
private def respond (program schema source value : String)
    (evaluate : Json → Json → Json → Except String (List (String × Json))) : String :=
  let result := do
    let schema ← (Json.parse schema).mapError ("schema: " ++ ·)
    let source ← (Json.parse source).mapError (s!"{program}: " ++ ·)
    let value ← (Json.parse value).mapError ("value: " ++ ·)
    evaluate schema source value
  encodeResponse result

@[export json_evaluate_typed]
def evaluateJsonTyped (schema expression value : String) : String :=
  respond "expression" schema expression value fun schema expression value =>
    (ExpressionProtocol.evaluateTyped schema expression value).map fun (schema, value) =>
      [("value", value), ("schema", schema.dataType.toJson)]

@[export json_check]
def checkJson (schema checker value : String) : String :=
  respond "checker" schema checker value fun schema checker value =>
    (CheckerProtocol.evaluate schema checker value).map fun errors => [("value", errors)]

@[export json_validate]
def validateJson (schema refinement value : String) : String :=
  respond "refinement" schema refinement value fun schema refinement value =>
    (ValidationProtocol.evaluate schema refinement value).map fun errors => [("value", errors)]

@[export json_normalize]
def normalizeJson (schema value : String) : String :=
  encodeResponse do
    let schema ← (Json.parse schema).mapError ("schema: " ++ ·)
    let value ← (Json.parse value).mapError ("value: " ++ ·)
    let normalized ← InputProtocol.evaluate schema value
    pure [("value", normalized)]

end WasmExperiment
