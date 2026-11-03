import Forms.Runtime.ExpressionProtocol

namespace Forms.Runtime.CheckerProtocol
open Lean Forms.Validation ExpressionProtocol

/-- Checker decoded into an executable function over wire schemas. -/
abbrev Program (root input : Schema) :=
  ⟦root.dataType⟧ → ⟦input.dataType⟧ → List (ResolvedError root.dataType)

private def location (input : Schema) : (target : Schema) → List Json →
    Except String (LocationExpr input.dataType target.dataType)
  | _, [] => pure .self
  | target, step :: rest =>
    (step.getObjValAs? String "kind").bind fun kind =>
    match kind, target with
    | "field", .record names _ fields =>
      (checkFields step ["kind", "name"]).bind fun _ =>
      (step.getObjValAs? String "name").bind fun name => do
      let some i := findName names name
        | .error s!"Unknown target field: {name}"
      (location input (fields i) rest).map (.field i)
    | "item", .list element =>
      (checkFields step ["kind", "index"]).bind fun _ =>
      (step.getObjVal? "index").bind fun index =>
      (decode input .natural index).bind fun index =>
      (location input element rest).map (.item index)
    | "constructor", .sum names _ branches =>
      (checkFields step ["kind", "tag"]).bind fun _ =>
      (step.getObjValAs? String "tag").bind fun tag => do
      let some i := findName names tag
        | .error s!"Unknown target constructor: {tag}"
      (location input (branches i) rest).map (.constructor i)
    | _, _ => throw s!"Invalid target step {kind} for {target.dataType.toJson.compress}"
termination_by _ steps => steps.length

private def targets (root input : Schema) (json : Json) :
    Except String (TargetsExpr root.dataType input.dataType) :=
  (json.getObjValAs? String "kind").bind fun kind =>
  match kind with
  | "global" => (checkFields json ["kind"]).map fun _ => .global
  | "fields" =>
    (checkFields json ["kind", "locations"]).bind fun _ =>
    (json.getObjVal? "locations").bind fun entries =>
    entries.getArr?.bind fun entries => do
    let locations ← entries.toList.mapM fun entry =>
      entry.getArr?.bind fun steps => location input root steps.toList
    if nonempty : locations ≠ [] then pure (.fields locations nonempty)
    else throw "Error locations must be nonempty"
  | kind => throw s!"Unknown target kind: {kind}"

private def iterationSchema (outer element : Schema) : Schema :=
  .record ["outer", "item", "index"] (by decide) fun i =>
    match i.val with
    | 0 => outer
    | 1 => element
    | _ => .natural

private def iterationValue {outer element : Schema}
    (context : ⟦outer.dataType⟧) (item : ⟦element.dataType⟧) (index : Nat) :
    ⟦(iterationSchema outer element).dataType⟧ :=
  fun i => match i with
    | ⟨0, _⟩ => context
    | ⟨1, _⟩ => item
    | ⟨_ + 2, _⟩ => index

/-- Decode every branch up front; expressions keep their checked types. -/
def decodeChecker (root input : Schema) (json : Json) : Except String (Program root input) :=
  (json.getObjValAs? String "kind").bind fun kind =>
  match kind with
  | "pass" =>
    (checkFields json ["kind"]).bind fun _ =>
    pure (fun _ _ => [])
  | "report" =>
    (checkFields json ["kind", "message", "targets"]).bind fun _ =>
    (json.getObjVal? "message").bind fun message =>
    (decode input .text message).bind fun message => do
    let target ← (json.getObjVal? "targets").bind (targets root input)
    pure (fun value context => [{ message := message.eval context, targets := target.resolve value context }])
  | "when" =>
    (checkFields json ["kind", "condition", "body"]).bind fun _ =>
    (json.getObjVal? "condition").bind fun condition =>
    (decode input .boolean condition).bind fun condition => do
    let body ← (childField json "body").bind fun body => decodeChecker root input body.val
    pure (fun value context => if condition.eval context then body value context else [])
  | "seq" =>
    (checkFields json ["kind", "left", "right"]).bind fun _ => do
    let left ← (childField json "left").bind fun left => decodeChecker root input left.val
    let right ← (childField json "right").bind fun right => decodeChecker root input right.val
    pure (fun value context => left value context ++ right value context)
  | "each" =>
    (checkFields json ["kind", "items", "body"]).bind fun _ =>
    (json.getObjVal? "items").bind fun items => do
    let ⟨.list element, items⟩ ← infer input items
      | throw "Validation iteration requires a list"
    let body ← (childField json "body").bind fun body =>
      decodeChecker root (iterationSchema input element) body.val
    pure (fun value context => (items.eval context).zipIdx.flatMap fun (item, index) =>
      body value (iterationValue context item index))
  | kind => throw s!"Unknown checker kind: {kind}"
termination_by sizeOf json
decreasing_by all_goals decreasing_tactic

def evaluate (schema checker value : Json) : Except String Json :=
  (Schema.fromJson schema).bind fun root =>
  (decodeChecker root root checker).bind fun program =>
  (JsonProtocol.valueFromJson root.dataType value).map fun value =>
    toJson ((program value value).map ResolvedError.toJson)

end Forms.Runtime.CheckerProtocol
