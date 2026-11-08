module

public import Forms.Model.Computation

@[expose] public section
namespace Forms.Model

inductive Editor : Type → Type where
  | text : Editor String
  | natural : Editor Nat
  | checkbox : Editor Bool

inductive Component (raw : Type) where
  | field {value : Type} (path : Path raw value) (label : String) (editor : Editor value)
  | group (label : String) (children : List (Component raw))
  | computed (label : String) (value : Computation raw String)
  | visibleWhen (condition : Computation raw Bool) (body : Component raw)
  | disabledWhen (condition : Computation raw Bool) (body : Component raw)


end Forms.Model
