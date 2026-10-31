import Forms.Core.Widget
import Forms.Core.Action
import Forms.Core.WidgetAction

namespace Forms.Composition

structure Column (row : DataType) where
  label : String
  format : Expr row .text

inductive Component : (state : DataType) → Type 1 where
  | field
      {state value : DataType}
      (path : Path state value)
      (label : String)
      (widget : Widget value)
      : Component state
  | stack
      {state : DataType}
      {items : Enum}
      (label : Option String := none)
      (children : items → Component state)
      (order : Equiv.Perm items := Equiv.refl _)
      : Component state
  | list
      {state element : DataType}
      (path : Path state (.list element))
      (label : String)
      (item : Component element)
      (defaultItem : ⟦element⟧)
      : Component state
  | sum
      {state : DataType}
      {tags : Enum}
      {constructors : tags → DataType}
      (path : Path state (.sum tags constructors))
      (label : String)
      (branches : (tag : tags) → Component (constructors tag))
      (defaults : (tag : tags) → ⟦constructors tag⟧)
      : Component state
  | computed
      {state result : DataType}
      (label : String)
      (expression : Expr state result)
      : Component state
  | text
      {state : DataType}
      (expression : Expr state .text)
      : Component state
  | table
      {state row : DataType}
      (rows : Expr state (.list row))
      (columns : List (Column row))
      : Component state
  | visibleWhen
      {state : DataType}
      (condition : Expr state .boolean)
      (body : Component state)
      : Component state
  | disabledWhen
      {state : DataType}
      (condition : Expr state .boolean)
      (body : Component state)
      : Component state
  | actionWidget {state value : DataType} {ids : Enum}
    (path : Path state value)
    (label : String)
    (actions : ids → WidgetAction value)
    : Component state
  | button {state : DataType}
    (label : String)
    (action : Action state)
    : Component state
  | appendItemButton
      {state element : DataType}
      (label : String)
      (target : Path state (.list element))
      (newItem : Expr state element)
      : Component state

def Component.weaken {outer inner : DataType}
  (path : Path outer inner)
  (body : Component inner)
  : Component outer :=
  match body with
  | .field target label widget => .field (path.trans target) label widget
  | .stack label children order => .stack label (fun index => (children index).weaken path) order
  | .list target label item defaultItem => .list (path.trans target) label item defaultItem
  | .sum target label branches defaults => .sum (path.trans target) label branches defaults
  | .computed label expression => .computed label (expression.weaken path)
  | .text expression => .text (expression.weaken path)
  | .table rows columns => .table (rows.weaken path) columns
  | .visibleWhen condition component => .visibleWhen (condition.weaken path) (component.weaken path)
  | .disabledWhen condition component => .disabledWhen (condition.weaken path) (component.weaken path)
  | .actionWidget target label actions => .actionWidget (path.trans target) label actions
  | .button label action => .button label (action.weaken path)
  | .appendItemButton label target newItem =>
      .appendItemButton label (path.trans target) (newItem.weaken path)

end Forms.Composition
