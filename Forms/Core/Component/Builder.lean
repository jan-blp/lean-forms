import Forms.Core.Composition

namespace Forms.Composition

/-- A reusable editor builder. Apply its target path to obtain an ordinary component. -/
abbrev Component.Builder (state value : DataType) := Path state value → Component state

namespace Component.Builder

def field {state value : DataType} (label : String) (widget : Widget value)
    : Component.Builder state value :=
  fun path => .field path label widget

def group {state : DataType} {fields : Enum} {types : fields → DataType}
    (label : String)
    (children : (i : fields) → Component.Builder state (types i))
    : Component.Builder state (.record fields types) :=
  fun path => .stack (some label) (fun i => children i (path.trans (.field i .self)))

def list {state element : DataType}
    (label : String)
    (item : Component.Builder element element)
    (defaultItem : ⟦element⟧)
    : Component.Builder state (.list element) :=
  fun path => .list path label (item .self) defaultItem

def visibleWhen {state value : DataType} (condition : Expr state .boolean)
    (body : Component.Builder state value) : Component.Builder state value :=
  fun path => .visibleWhen condition (body path)

end Component.Builder
end Forms.Composition
