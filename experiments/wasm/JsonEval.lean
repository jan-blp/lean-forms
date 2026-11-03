import Forms.Runtime.CheckerProtocol

namespace WasmExperiment
open Lean Forms.Runtime

/-- A single transport boundary: parse, decode, evaluate, then serialize. -/
private def respond (program schema source value : String)
    (evaluate : Json → Json → Json → Except String (List (String × Json))) : String :=
  let result := do
    let schema ← (Json.parse schema).mapError ("schema: " ++ ·)
    let source ← (Json.parse source).mapError (s!"{program}: " ++ ·)
    let value ← (Json.parse value).mapError ("value: " ++ ·)
    evaluate schema source value
  (match result with
    | .ok fields => Json.mkObj (("ok", toJson true) :: fields)
    | .error error => Json.mkObj [("ok", toJson false), ("error", toJson error)]).compress

private def run (typed : Bool) (schema expression value : String) : String :=
  respond "expression" schema expression value fun schema expression value =>
    (ExpressionProtocol.evaluateTyped schema expression value).map fun (schema, value) =>
      ("value", value) :: if typed then [("schema", schema.dataType.toJson)] else []

@[export json_evaluate]
def evaluateJson (schema expression value : String) : String := run false schema expression value

@[export json_evaluate_typed]
def evaluateJsonTyped (schema expression value : String) : String := run true schema expression value

@[export json_check]
def checkJson (schema checker value : String) : String :=
  respond "checker" schema checker value fun schema checker value =>
    (CheckerProtocol.evaluate schema checker value).map fun errors => [("value", errors)]

end WasmExperiment
