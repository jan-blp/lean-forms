module

public import Forms.ExampleForms.Example
public import Forms.Runtime.CompiledView
public import Forms.Runtime.CompositionProtocol

@[expose] public section

namespace Forms.Runtime.CompiledForms
open Lean Composition ExampleForms

/-- Client validation deliberately excludes server-only checks. -/
def clientErrors {ty : DataType} (refined : RefinedDataType ty) (value : ⟦ty⟧) :
    List (Validation.ResolvedError ty) :=
  match refined, value with
  | .base _, _ => []
  | .refine inner checked, value => clientErrors inner value ++ checked.checker.run value
  | .serverRefine inner _, value => clientErrors inner value
  | .list item, values => values.zipIdx.flatMap fun (value, index) =>
      (clientErrors item value).map (·.mapLocations (.item index))
  | .record fields, value => (FinEnum.toList _).flatMap fun name =>
      (clientErrors (fields name) (value name)).map (·.mapLocations (.field name))
  | .sum branches, value =>
      (clientErrors (branches value.tag) value.payload).map (·.mapLocations (.constructor value.tag))

/-- A deterministic compatibility stamp, not a security hash. Excludes initial values. -/
def revision (definition : Example.Definition) : String :=
  let source := (Json.mkObj [("schema", definition.ty.toJson),
    ("form", CompositionProtocol.componentToJson definition.component),
    ("validation", definition.refined.toJson)]).compress
  let digest := source.toUTF8.foldl (fun (h : UInt64) byte =>
    (h ^^^ byte.toUInt64) * 1099511628211) 14695981039346656037
  "compiled-1-" ++ toString digest

def descriptor (selected : Example) : Json :=
  let definition := selected.definition
  Json.mkObj [("form", toJson selected.name), ("revision", toJson (revision definition)),
    ("value", JsonProtocol.valueToJson definition.initial)]

structure Model (selected : Example) where
  initial : ⟦selected.definition.ty⟧
  history : ComponentHistory selected.definition.component

def openModel (request : Json) : Except String ((selected : Example) × Model selected) := do
  let name ← request.getObjValAs? String "form"
  let some selected := Example.ofName name | throw s!"Unknown compiled form: {name}"
  let definition := selected.definition
  let expected ← request.getObjValAs? String "revision"
  unless expected == revision definition do
    throw "Compiled form version differs from the server. Rebuild Wasm and reload."
  let initial ← JsonProtocol.valueFromJson definition.ty (← request.getObjVal? "value")
  pure ⟨selected, { initial, history := { value := initial } }⟩

def snapshot {selected : Example} (model : Model selected) : Json :=
  let rendered := CompiledView.render selected.definition.component model.history.value
  let title := match rendered.view.getObjValAs? String "label" with
    | .ok label => if label.isEmpty then "Form" else label
    | .error _ => "Form"
  Json.mkObj [("view", rendered.view), ("controls", toJson (rendered.controls.map (·.view))),
    ("title", toJson title), ("submission", ComponentHistoryProtocol.encode model.history),
    ("errors", toJson ((clientErrors selected.definition.refined model.history.value).map Validation.ResolvedError.toJson))]

def apply {selected : Example} (model : Model selected) (request : Json) : Except String (Model selected) := do
  let key ← request.getObjValAs? String "key"
  let invocation ← CompiledView.invocation selected.definition.component model.history.value key
    (request.getObjVal? "argument").toOption
  let history ← (model.history.apply invocation).mapError toString
  pure { model with history }

/-- IDs are never reused: disposed handles cannot address a later model. -/
structure Store where
  next : Nat := 0
  models : List (Nat × ((selected : Example) × Model selected)) := []
  deriving Inhabited

def execute (store : Store) (request : Json) : Except String (Store × Json) := do
  let operation ← request.getObjValAs? String "operation"
  if operation == "open" then
    let model ← openModel request
    pure ({ next := store.next + 1, models := (store.next, model) :: store.models },
      Json.mkObj [("handle", toJson (toString store.next)), ("snapshot", snapshot model.2)])
  else
    let idText ← request.getObjValAs? String "handle"
    let some id := idText.toNat? | throw "Invalid form handle"
    let some (_, ⟨selected, model⟩) := store.models.find? (·.1 == id) | throw "Unknown or disposed form handle"
    if operation == "dispose" then
      pure ({ store with models := store.models.filter (·.1 != id) }, Json.null)
    else
      let model ← match operation with
        | "apply" => apply model request
        | "reset" => pure { model with history := { value := model.initial } }
        | "inspect" => pure model
        | _ => throw s!"Unknown form operation: {operation}"
      let response := snapshot model
      pure ({ store with models := store.models.map fun (key, current) =>
        (key, if key == id then ⟨selected, model⟩ else current) }, response)

end Forms.Runtime.CompiledForms
