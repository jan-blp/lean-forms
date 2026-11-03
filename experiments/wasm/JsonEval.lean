import Forms.Runtime.ExpressionProtocol

namespace WasmExperiment
open Lean Forms.Runtime

/-- A single transport boundary: parse, type-check, evaluate, then serialize. -/
private def run (typed : Bool) (schema expression value : String) : String :=
  let evaluated : Except String (ExpressionProtocol.Schema × Json) := do
    let schema ← (Json.parse schema).mapError ("schema: " ++ ·)
    let expression ← (Json.parse expression).mapError ("expression: " ++ ·)
    let value ← (Json.parse value).mapError ("value: " ++ ·)
    ExpressionProtocol.evaluateTyped schema expression value
  let response := match evaluated with
    | .ok (schema, value) => Json.mkObj ([("ok", toJson true), ("value", value)] ++
        if typed then [("schema", schema.dataType.toJson)] else [])
    | .error error => Json.mkObj [("ok", toJson false), ("error", toJson error)]
  response.compress

@[export json_evaluate]
def evaluateJson (schema expression value : String) : String := run false schema expression value

@[export json_evaluate_typed]
def evaluateJsonTyped (schema expression value : String) : String := run true schema expression value

end WasmExperiment
