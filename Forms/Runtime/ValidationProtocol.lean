module

public import Forms.Runtime.CheckerProtocol

@[expose] public section

namespace Forms.Runtime.ValidationProtocol
open Lean Forms.Validation ExpressionProtocol

/-- A decoded client refinement over a checked wire schema. -/
abbrev Program (schema : Schema) :=
  ⟦schema.dataType⟧ → List (ResolvedError schema.dataType)

/-- Decode all refinements, including empty lists and inactive sum branches. -/
def decode (schema : Schema) (json : Json) : Except String (Program schema) :=
  (json.getObjValAs? String "kind").bind fun kind =>
  match kind, schema with
  | "base", _ => (checkFields json ["kind"]).map fun _ _ => []
  | "refine", schema =>
    (checkFields json ["kind", "inner", "checker"]).bind fun _ => do
    let inner ← (childField json "inner").bind fun inner => decode schema inner.val
    let checker ← (json.getObjVal? "checker").bind (CheckerProtocol.decodeChecker schema schema)
    pure (fun value => inner value ++ checker value value)
  | "list", .list element =>
    (checkFields json ["kind", "item"]).bind fun _ => do
    let item ← (childField json "item").bind fun item => decode element item.val
    pure (fun values => values.zipIdx.flatMap fun (value, index) =>
      (item value).map (·.mapLocations (.item index)))
  | "record", .record names _ types =>
    (checkFields json ["kind", "fields"]).bind fun _ => do
    (childField json "fields").bind fun fields =>
    (checkFields fields.val names).bind fun _ => do
    let decoded ← JsonProtocol.sequenceFin (n := names.length) fun i =>
      (childField fields.val (names.get i)).bind fun field => decode (types i) field.val
    pure (fun value => (List.finRange names.length).flatMap fun i =>
      (decoded i (value i)).map (·.mapLocations (.field i)))
  | "sum", .sum names _ types =>
    (checkFields json ["kind", "branches"]).bind fun _ => do
    (childField json "branches").bind fun branches =>
    (checkFields branches.val names).bind fun _ => do
    let decoded ← JsonProtocol.sequenceFin (n := names.length) fun i =>
      (childField branches.val (names.get i)).bind fun branch => decode (types i) branch.val
    pure (fun value =>
      (decoded value.tag value.payload).map (·.mapLocations (.constructor value.tag)))
  | kind, _ => throw s!"Invalid refinement kind {kind} for {schema.dataType.toJson.compress}"
termination_by sizeOf json
decreasing_by all_goals decreasing_tactic

def evaluate (schema refinement value : Json) : Except String Json :=
  (Schema.fromJson schema).bind fun schema =>
  (decode schema refinement).bind fun program =>
  (JsonProtocol.valueFromJson schema.dataType value).map fun value =>
    toJson ((program value).map ResolvedError.toJson)

end Forms.Runtime.ValidationProtocol
