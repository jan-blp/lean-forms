import Forms.Runtime.ExpressionProtocol.Schema

namespace Forms.Runtime.ExpressionProtocol
open Lean

/-- A decoded expression carries its checked result schema. -/
abbrev Decoded (input : Schema) := (result : Schema) × Forms.Expr input.dataType result.dataType

def requireType {input : Schema} (expected : Schema) (decoded : Decoded input)
    : Except String (Forms.Expr input.dataType expected.dataType) :=
  if same : decoded.1 = expected then .ok (same ▸ decoded.2)
  else .error s!"Type mismatch: expected {expected.dataType.toJson.compress}, got {decoded.1.dataType.toJson.compress}"

/-- Index of the label equal to `name`. -/
def findName (names : List String) (name : String) : Option (Fin names.length) :=
  (List.finRange names.length).find? (fun i => names.get i == name)

def pathFromLabels (input : Schema) (labels : List String)
    : Except String ((result : Schema) × Path input.dataType result.dataType) :=
  match labels, input with
  | [], input => pure ⟨input, .self⟩
  | name :: rest, .record names _ fields =>
      match findName names name with
      | none => .error s!"Unknown field: {name}"
      | some index => (pathFromLabels (fields index) rest).map fun ⟨result, path⟩ =>
          ⟨result, .field index path⟩
  | _ :: _, _ => .error "A field path must traverse a record"

def expressionKind (json : Json) : Except String String := do
  let kind ← json.getObjValAs? String "kind"
  let fields ← match kind with
    | "value" => pure ["type", "value"]
    | "project" => pure ["path"]
    | "natAdd" | "natSub" | "natMul" | "natLe" | "textEq" | "textAppend"
    | "dateLe" | "and" | "enumEq" => pure ["left", "right"]
    | "not" | "natToText" => pure ["operand"]
    | "ifThenElse" => pure ["condition", "whenTrue", "whenFalse"]
    | "all" | "filter" => pure ["items", "predicate"]
    | "sum" => pure ["items", "expression"]
    | "length" => pure ["items"]
    | "snoc" => pure ["items", "value"]
    | "sortBy" | "sortNatBy" => pure ["items", "key", "descending"]
    | "search" => pure ["items", "key", "query"]
    | "enumLabel" => pure ["subject", "options"]
    | "enumCases" | "cases" => pure ["type", "subject", "branches"]
    | _ => throw s!"Unknown expression kind: {kind}"
  checkFields json ("kind" :: fields)
  return kind

/-- Decode and type-check the existing expression wire format. No evaluation occurs here. -/
def infer (input : Schema) (json : Json) : Except String (Decoded input) :=
  (expressionKind json).bind fun kind => do
  -- Except.bind also connects JSON (Type) to typed expressions (Type 1).
  let childAt (context : Schema) (key : String) : Except String (Decoded context) :=
    (childField json key).bind fun value =>
      (infer context value.val).mapError (fun error => s!"{kind}.{key}: {error}")
  let child := childAt input
  let checked (expected : Schema) (key : String) : Except String (Forms.Expr input.dataType expected.dataType) := do
    requireType expected (← child key)
  match kind with
  | "value" =>
      (json.getObjVal? "type").bind fun type => (Schema.fromJson type).bind fun result =>
        (json.getObjVal? "value").bind fun value =>
          (JsonProtocol.valueFromJson result.dataType value).map fun decoded => ⟨result, .value decoded⟩
  | "project" =>
      (json.getObjValAs? (List String) "path").bind fun labels =>
        (pathFromLabels input labels).map fun ⟨result, path⟩ => ⟨result, .project path⟩
  | "natAdd" | "natSub" | "natMul" | "natLe" =>
      let left ← checked .natural "left"
      let right ← checked .natural "right"
      match kind with
      | "natAdd" => return ⟨.natural, .natAdd left right⟩
      | "natSub" => return ⟨.natural, .natSub left right⟩
      | "natMul" => return ⟨.natural, .natMul left right⟩
      | _ => return ⟨.boolean, .natLe left right⟩
  | "textEq" | "textAppend" =>
      let left ← checked .text "left"
      let right ← checked .text "right"
      if kind == "textEq" then return ⟨.boolean, .textEq left right⟩
      else return ⟨.text, .textAppend left right⟩
  | "dateLe" =>
      return ⟨.boolean, .dateLe (← checked .date "left") (← checked .date "right")⟩
  | "and" =>
      return ⟨.boolean, .and (← checked .boolean "left") (← checked .boolean "right")⟩
  | "not" =>
      return ⟨.boolean, .not (← checked .boolean "operand")⟩
  | "natToText" =>
      return ⟨.text, .natToText (← checked .natural "operand")⟩
  | "ifThenElse" =>
      let condition ← checked .boolean "condition"
      let ⟨result, whenTrue⟩ ← child "whenTrue"
      return ⟨result, .ifThenElse condition whenTrue (← checked result "whenFalse")⟩
  | "all" | "filter" =>
      let ⟨.list element, items⟩ ← child "items" | throw "Expected list items"
      let predicate ← requireType .boolean (← childAt element "predicate")
      if kind == "all" then return ⟨.boolean, .all items predicate⟩
      else return ⟨.list element, .filter items predicate⟩
  | "sum" =>
      let ⟨.list element, items⟩ ← child "items" | throw "Expected list items"
      let body ← requireType .natural (← childAt element "expression")
      return ⟨.natural, .sum items body⟩
  | "length" =>
      let ⟨.list _, items⟩ ← child "items" | throw "Expected list items"
      return ⟨.natural, .length items⟩
  | "snoc" =>
      let ⟨.list element, items⟩ ← child "items" | throw "Expected list items"
      return ⟨.list element, .snoc items (← checked element "value")⟩
  | "sortBy" | "sortNatBy" =>
      let ⟨.list element, items⟩ ← child "items" | throw "Expected list items"
      (json.getObjValAs? Bool "descending").bind fun descending => do
      let key ← childAt element "key"
      if kind == "sortBy" then return ⟨.list element, .sortBy items (← requireType .text key) descending⟩
      else return ⟨.list element, .sortNatBy items (← requireType .natural key) descending⟩
  | "search" =>
      let ⟨.list element, items⟩ ← child "items" | throw "Expected list items"
      let key ← requireType .text (← childAt element "key")
      return ⟨.list element, .search items key (← checked .text "query")⟩
  | "enumEq" =>
      let ⟨.enum names unique, left⟩ ← child "left" | throw "Expected enum operand"
      return ⟨.boolean, .enumEq left (← checked (.enum names unique) "right")⟩
  | "enumLabel" =>
      let ⟨.enum names _, subject⟩ ← child "subject" | throw "Expected enum subject"
      (json.getObjValAs? (List String) "options").bind fun options => do
      if options != names then throw "Enum label options do not match the subject"
      return ⟨.text, .enumLabel subject⟩
  | "enumCases" =>
      let ⟨.enum names unique, subject⟩ ← child "subject" | throw "Expected enum subject"
      (json.getObjVal? "type").bind fun type => (Schema.fromJson type).bind fun result =>
      (childField json "branches").bind fun container => (childElements container.val).bind fun branches => do
      if branches.size != names.length then throw "Wrong number of enum branches"
      let decoded ← JsonProtocol.sequenceFin (n := names.length) fun i => do
        let some branch := branches[i.val]? | throw "Missing enum branch"
        requireType result (← infer input branch.val)
      return ⟨result, .enumCases (domain := domain names unique) subject decoded⟩
  | "cases" =>
      let ⟨.sum names unique types, subject⟩ ← child "subject" | throw "Expected sum subject"
      (json.getObjVal? "type").bind fun type => (Schema.fromJson type).bind fun result =>
      (childField json "branches").bind fun branches =>
      (checkFields branches.val names).bind fun _ => do
      let decoded ← JsonProtocol.sequenceFin (n := names.length) fun i =>
        (childField branches.val (names.get i)).bind fun branch => do
          requireType result (← infer (types i) branch.val)
      return ⟨result, .cases (tags := domain names unique) subject decoded⟩
  | _ => throw s!"Unknown expression kind: {kind}"

termination_by sizeOf json
decreasing_by all_goals decreasing_tactic

/-- Decode with an expected result schema when the surrounding component supplies one. -/
def decode (input result : Schema) (json : Json)
    : Except String (Forms.Expr input.dataType result.dataType) := do
  requireType result (← infer input json)

/-- Preserve the inferred result schema for callers evaluating nested scopes. -/
def evaluateTyped (inputSchema expression value : Json) : Except String (Schema × Json) :=
  (Schema.fromJson inputSchema).bind fun input =>
    (infer input expression).bind fun ⟨result, decoded⟩ => do
      let argument ← JsonProtocol.valueFromJson input.dataType value
      return (result, JsonProtocol.valueToJson (decoded.eval argument))

/-- A JSON boundary for the evaluator, shared by native tests and the Wasm adapter. -/
def evaluate (inputSchema expression value : Json) : Except String Json :=
  (evaluateTyped inputSchema expression value).map Prod.snd

end Forms.Runtime.ExpressionProtocol
