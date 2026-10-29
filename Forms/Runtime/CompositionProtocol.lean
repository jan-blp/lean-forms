import Forms.Core.Composition
import Forms.Runtime.JsonProtocol

namespace Forms.Runtime.CompositionProtocol
open Lean Composition

def componentToJson {state : DataType} (component : Component state) : Json :=
  match component with
  | .field (value := value) path label widget => Json.mkObj [
      ("kind", toJson "field"), ("path", toJson (Path.toList path)),
      ("schema", DataType.toJson value), ("label", toJson label), ("widget", toJson (Widget.name widget))]
  | .list (element := element) path label item defaultItem => Json.mkObj [
      ("kind", toJson "list"), ("path", toJson (Path.toList path)),
      ("schema", DataType.toJson (.list element)), ("label", toJson label),
      ("item", componentToJson item), ("defaultItem", JsonProtocol.valueToJson defaultItem)]
  | .sum (tags := tags) (constructors := constructors) path label branches defaults => Json.mkObj [
      ("kind", toJson "sum"), ("path", toJson (Path.toList path)),
      ("schema", DataType.toJson (.sum tags constructors)), ("label", toJson label),
      ("branches", Json.mkObj ((FinEnum.toList tags).map fun tag => (tags.label tag, componentToJson (branches tag)))),
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
      ("kind", toJson "visibleWhen"), ("condition", Expr.toJson condition), ("body", componentToJson body)]
  | .disabledWhen condition body => Json.mkObj [
      ("kind", toJson "disabledWhen"), ("condition", Expr.toJson condition), ("body", componentToJson body)]
  | .appendItemButton label target newItem => Json.mkObj [
      ("kind", toJson "appendItemButton"), ("label", toJson label),
      ("path", toJson (Path.toList target)), ("value", Expr.toJson newItem)]
  | .stack (items := items) label children order => Json.mkObj [
      ("kind", toJson "stack"), ("label", toJson label),
      ("children", toJson ((FinEnum.toList items).map fun index => componentToJson (children (order index))))]

def encode {state : DataType} (refined : RefinedDataType state) (component : Component state)
    (draft : ⟦state⟧) : String :=
  (Json.mkObj [
    ("version", toJson (4 : Nat)), ("schema", DataType.toJson state),
    ("constraints", toJson ((RefinedDataType.constraints refined).map Constraint.toJson)),
    ("form", componentToJson component), ("value", JsonProtocol.valueToJson draft)]).compress

end Forms.Runtime.CompositionProtocol
