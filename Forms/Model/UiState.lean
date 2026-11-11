module

public import Lean.Data.Json
public import Std.Data.HashMap

@[expose] public section
namespace Forms.Model

/-- A key to a shared UI value. Scoped to a form -/
structure UiStateKey (value : Type) where
  key : String
  initial : value

/-- Component state kept separately from the form's submitted value. -/
structure UiState where
  values : Std.HashMap String Lean.Json := {}

def UiStateKey.get {α : Type} [Lean.FromJson α] (key : UiStateKey α)
    (state : UiState) : α :=
  ((state.values[key.key]?).bind fun json => (Lean.fromJson? json).toOption).getD key.initial

def UiStateKey.set {α : Type} [Lean.ToJson α] (key : UiStateKey α)
    (value : α) (state : UiState) : UiState :=
  { state with values := state.values.insert key.key (Lean.toJson value) }

end Forms.Model
