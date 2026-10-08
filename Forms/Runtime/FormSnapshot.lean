import Forms.Core.Composition

namespace Forms

inductive FieldContent (t : DataType) where
  | input (widget : Widget t)
  | computed (value : ⟦t⟧)

structure FieldRef where
  {t : DataType}
  content : FieldContent t
  labels : List String
  indices : List Nat
  disabled : Bool := false

end Forms

namespace Forms.Runtime
open Composition

inductive FormSnapshot where
  | fields (values : List FieldRef)
  | text (value : String)
  | action (label : String) (disabled : Bool := false)
  | table (headings : List String) (rows : List (List String))
  | stack (children : List FormSnapshot)

private def mapFields (f : FieldRef → FieldRef) : FormSnapshot → FormSnapshot
  | .fields fields => .fields (fields.map f)
  | .stack children => .stack (children.map (mapFields f))
  | other => other

private def disable : FormSnapshot → FormSnapshot
  | .fields fields => .fields (fields.map fun field => { field with disabled := true })
  | .action label _ => .action label true
  | .stack children => .stack (children.map disable)
  | other => other

private def pathIndices {state value : DataType} : Path state value → List Nat
  | .self => []
  | .field name rest => (FinEnum.equiv name).val :: pathIndices rest

def FormSnapshot.render {state : DataType} (component : Component state)
    (value : ⟦state⟧) : FormSnapshot :=
  match component with
  | .field path label widget =>
      .fields [{ content := .input widget, labels := [label], indices := pathIndices path }]
  | .visibleWhen condition body =>
      if condition.eval value then render body value else .stack []
  | .stack (items := items) label children =>
      let snapshot := .stack ((FinEnum.toList items).map fun i => render (children i) value)
      match label with
      | none => snapshot
      | some label => mapFields (fun field => { field with labels := label :: field.labels }) snapshot

def FormSnapshot.fieldRefs : FormSnapshot → List FieldRef
  | .fields values => values
  | .stack children => children.flatMap FormSnapshot.fieldRefs
  | _ => []

end Forms.Runtime
