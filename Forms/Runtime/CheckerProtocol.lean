module

public import Forms.Runtime.ExpressionProtocol

@[expose] public section

namespace Forms.Runtime.CheckerProtocol
open Lean Forms.Validation ExpressionProtocol

/-- Checker decoded into an executable function over wire schemas. -/
abbrev Program (root input : Schema) :=
  ⟦root.dataType⟧ → ⟦input.dataType⟧ → List (ResolvedError root.dataType)

def location (input : Schema) : (target : Schema) → List Json →
    Except String (⟦input.dataType⟧ → Location target.dataType)
  | _, [] => pure (fun _ => .self)
  | target, step :: rest =>
    (step.getObjValAs? String "kind").bind fun kind =>
    match kind, target with
    | "field", .record names _ fields =>
      (checkFields step ["kind", "name"]).bind fun _ =>
      (step.getObjValAs? String "name").bind fun name => do
      let some i := findName names name
        | .error s!"Unknown target field: {name}"
      (location input (fields i) rest).map (fun rest context => .field i (rest context))
    | "item", .list element =>
      (checkFields step ["kind", "index"]).bind fun _ =>
      (step.getObjVal? "index").bind fun index =>
      (decode input .natural index).bind fun index =>
      (location input element rest).map (fun rest context => .item (index.eval context) (rest context))
    | "constructor", .sum names _ branches =>
      (checkFields step ["kind", "tag"]).bind fun _ =>
      (step.getObjValAs? String "tag").bind fun tag => do
      let some i := findName names tag
        | .error s!"Unknown target constructor: {tag}"
      (location input (branches i) rest).map (fun rest context => .constructor i (rest context))
    | _, _ => throw s!"Invalid target step {kind} for {target.dataType.toJson.compress}"
termination_by _ steps => steps.length

def targets (root input : Schema) (json : Json) :
    Except String (⟦root.dataType⟧ → ⟦input.dataType⟧ → TargetResolution root.dataType) :=
  (json.getObjValAs? String "kind").bind fun kind =>
  match kind with
  | "global" => (checkFields json ["kind"]).map fun _ _ _ => .global
  | "locations" =>
    (checkFields json ["kind", "locations"]).bind fun _ =>
    (json.getObjVal? "locations").bind fun entries =>
    entries.getArr?.bind fun entries => do
    let locations ← entries.toList.mapM fun entry =>
      entry.getArr?.bind fun steps => location input root steps.toList
    if nonempty : locations ≠ [] then pure (fun value context =>
      let resolved := locations.map (fun location => location context)
      match resolved.find? (fun location => !location.exists value) with
      | some location => .invalidTarget location
      | none => .locations resolved (by simpa [resolved] using nonempty))
    else throw "Error locations must be nonempty"
  | kind => throw s!"Unknown target kind: {kind}"

def branchSchema (outer payload : Schema) : Schema :=
  .record ["outer", "payload"] (by decide) fun i =>
    match i.val with | 0 => outer | _ => payload

def branchValue {outer payload : Schema}
    (context : ⟦outer.dataType⟧) (value : ⟦payload.dataType⟧) :
    ⟦(branchSchema outer payload).dataType⟧ :=
  fun i => match i with | ⟨0, _⟩ => context | ⟨_ + 1, _⟩ => value

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
    pure (fun value context => [{ message := message.eval context, targets := target value context }])
  | "ite" =>
    (checkFields json ["kind", "condition", "thenBranch", "elseBranch"]).bind fun _ =>
    (json.getObjVal? "condition").bind fun condition =>
    (decode input .boolean condition).bind fun condition => do
    let yes ← (childField json "thenBranch").bind fun body => decodeChecker root input body.val
    let no ← (childField json "elseBranch").bind fun body => decodeChecker root input body.val
    pure (fun value context => if condition.eval context then yes value context else no value context)
  | "cases" =>
    (checkFields json ["kind", "subject", "branches"]).bind fun _ =>
    (json.getObjVal? "subject").bind fun subject => do
    let ⟨.sum names unique types, subject⟩ ← infer input subject
      | throw "Validation cases requires a sum"
    (childField json "branches").bind fun branches =>
    (checkFields branches.val names).bind fun _ => do
    let decoded ← JsonProtocol.sequenceFin (n := names.length) fun i =>
      (childField branches.val (names.get i)).bind fun branch =>
        decodeChecker root (branchSchema input (types i)) branch.val
    pure (fun value context =>
      let selected := subject.eval context
      decoded selected.tag value (branchValue context selected.payload))
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
