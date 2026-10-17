import Forms.Core.Composition

namespace Forms.Composition

/-- A reusable editor builder. Apply its target path to obtain an ordinary component. -/
abbrev Component.Builder (state value : DataType) := Path state value → Component state

private inductive PairSection where
  | body
  | extra
  deriving DecidableEq

private instance : FinEnum PairSection :=
  FinEnum.ofList [.body, .extra] (by grind [PairSection])

private def pairFields : Enum where
  type := PairSection
  label
    | .body => "body"
    | .extra => "extra"

namespace Component.Builder

def field {state value : DataType} (label : String) (widget : Widget value)
    : Component.Builder state value :=
  fun path => .field path label widget

def group {state : DataType} {fields : Enum} {types : fields → DataType}
    (label : String)
    (children : (i : fields) → Component.Builder state (types i))
    (displayOrder : Equiv.Perm fields := Equiv.refl _)
    : Component.Builder state (.record fields types) :=
  fun path => .stack (some label) (fun i => children i (path.trans (.field i .self))) displayOrder

def list {state element : DataType}
    (label : String)
    (item : Component.Builder element element)
    (defaultItem : ⟦element⟧)
    : Component.Builder state (.list element) :=
  fun path => .list path label (item .self) defaultItem

def sum {state : DataType} {tags : Enum} {constructors : tags → DataType}
    (label : String)
    (branches : (tag : tags) → Component.Builder (constructors tag) (constructors tag))
    (defaults : (tag : tags) → ⟦constructors tag⟧)
    : Component.Builder state (.sum tags constructors) :=
  fun path => .sum path label (fun tag => branches tag .self) defaults

def visibleWhen {state value : DataType} (condition : Expr state .boolean)
    (body : Component.Builder state value) : Component.Builder state value :=
  fun path => .visibleWhen condition (body path)

def disabledWhen {state value : DataType} (condition : Expr state .boolean)
    (body : Component.Builder state value) : Component.Builder state value :=
  fun path => .disabledWhen condition (body path)

def computed {state value result : DataType}
    (label : String) (expression : Expr state result)
    (body : Component.Builder state value) : Component.Builder state value :=
  fun path => .stack none (items := pairFields) fun
    | .body => body path
    | .extra => .computed label expression

end Component.Builder
end Forms.Composition
