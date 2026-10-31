import Forms.Core.ComponentHistory
import Forms.Runtime.JsonProtocol

namespace Forms.Runtime.CompositionProtocol
open Lean Composition

def actionToJson {state : DataType} : Action state → Json
  | .set target replacement => Json.mkObj [
      ("kind", toJson "set"), ("path", toJson (Path.toList target)),
      ("value", Expr.toJson replacement)]
  | .append target expression => Json.mkObj [
      ("kind", toJson "append"), ("path", toJson (Path.toList target)),
      ("value", Expr.toJson expression)]

def widgetActionToJson {value : DataType}
  (id : String)
  (action : WidgetAction value)
  : Json :=
  Json.mkObj ([("id", toJson id), ("label", toJson action.label)] ++
    match action.presentation with
    | .button body => [("kind", toJson "button"), ("body", Expr.toJson body)]
    | .editor widget body => [("kind", toJson "editor"),
        ("widget", toJson (Widget.name widget)), ("body", Expr.toJson body)])

def componentToJson {state : DataType}
  (component : Component state)
  (history : Bool := false)
  : Json :=
  match component with
  | .field (value := value) path label widget => Json.mkObj [
      ("kind", toJson "field"), ("path", toJson (Path.toList path)),
      ("schema", DataType.toJson value), ("label", toJson label), ("widget", toJson (Widget.name widget))]
  | .list (element := element) path label item defaultItem => Json.mkObj [
      ("kind", toJson "list"), ("path", toJson (Path.toList path)),
      ("schema", DataType.toJson (.list element)), ("label", toJson label),
      ("item", componentToJson item history), ("defaultItem", JsonProtocol.valueToJson defaultItem)]
  | .sum (tags := tags) (constructors := constructors) path label branches defaults => Json.mkObj [
      ("kind", toJson "sum"), ("path", toJson (Path.toList path)),
      ("schema", DataType.toJson (.sum tags constructors)), ("label", toJson label),
      ("branches", Json.mkObj ((FinEnum.toList tags).map fun tag => (tags.label tag, componentToJson (branches tag) history))),
      ("defaults", Json.mkObj ((FinEnum.toList tags).map fun tag => (tags.label tag, JsonProtocol.valueToJson (defaults tag))))]
  | .computed (result := result) label expression => Json.mkObj [
      ("kind", toJson "computed"), ("label", toJson label),
      ("type", DataType.toJson result), ("expression", Expr.toJson expression)]
  | .text expression => Json.mkObj [("kind", toJson "text"), ("expression", Expr.toJson expression)]
  | .table rows columns => Json.mkObj [
      ("kind", toJson "table"), ("rows", Expr.toJson rows),
      ("columns", toJson (columns.map fun column => Json.mkObj [
        ("label", toJson column.label), ("expression", Expr.toJson column.format)]))]
  | .visibleWhen condition body => Json.mkObj [
      ("kind", toJson "visibleWhen"), ("condition", Expr.toJson condition), ("body", componentToJson body history)]
  | .disabledWhen condition body => Json.mkObj [
      ("kind", toJson "disabledWhen"), ("condition", Expr.toJson condition), ("body", componentToJson body history)]
  | .actionWidget (value := value) (ids := ids) path label actions => Json.mkObj [
      ("kind", toJson "actionWidget"), ("path", toJson (Path.toList path)),
      ("schema", DataType.toJson value), ("label", toJson label),
      ("actions", toJson ((FinEnum.toList ids).map fun id => widgetActionToJson (ids.label id) (actions id)))]
  | .button label action => Json.mkObj [
      ("kind", toJson "button"), ("label", toJson label), ("action", actionToJson action)]
  | .stack (items := items) label children order => Json.mkObj ([
      ("kind", toJson "stack"), ("label", toJson label),
      ("children", toJson ((FinEnum.toList items).map fun index => componentToJson (children (order index)) history))] ++
      if history then [("childIds", toJson ((FinEnum.toList items).map fun index => items.label (order index)))] else [])

def encode {state : DataType}
  (refined : RefinedDataType state)
  (component : Component state)
  (draft : ⟦state⟧)
  : String :=
  (Json.mkObj [
    ("version", toJson (if component.supportsHistory then (6 : Nat) else 4)), ("schema", DataType.toJson state),
    ("constraints", toJson ((RefinedDataType.constraints refined).map Constraint.toJson)),
    ("form", componentToJson component component.supportsHistory), ("value", JsonProtocol.valueToJson draft)]).compress

end Forms.Runtime.CompositionProtocol
