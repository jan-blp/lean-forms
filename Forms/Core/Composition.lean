import Forms.Core.Widget

namespace Forms.Composition

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
      : Component state
  | list
      {state element : DataType}
      (path : Path state (.list element))
      (label : String)
      (item : Component element)
      (defaultItem : ⟦element⟧)
      : Component state
  | visibleWhen
      {state : DataType}
      (condition : Expr state .boolean)
      (body : Component state)
      : Component state

end Forms.Composition
