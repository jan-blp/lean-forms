module

public import Forms.Model.Context

@[expose] public section
namespace Forms.Model

/-- Why an invocation does not apply to the current value. -/
inductive InvocationError where
  | hidden
  | disabled
  | inactiveBranch
  | indexOutOfBounds (index length : Nat)
  /-- No control with the key is shown. -/
  | absent
  /-- The choice has no branch with the requested key. -/
  | unavailableBranch (key : String)
  deriving DecidableEq, Repr

instance : ToString InvocationError where
  toString
    | .hidden => "This action is unavailable: the control is hidden."
    | .disabled => "This action is unavailable: the control is disabled."
    | .inactiveBranch => "This action is unavailable: the option is not selected."
    | .indexOutOfBounds index length =>
      s!"This action is unavailable: item {index + 1} of {length}."
    | .absent => "This action is unavailable: the control is no longer shown."
    | .unavailableBranch key => s!"This action is unavailable: branch '{key}' is no longer available."

/-- The model, context, and local bindings after a checked invocation. -/
structure ComponentUpdate (Γ : Context) (α localState : Type) where
  value : α
  state : Env Γ
  locals : localState

def ComponentUpdate.mapValue
  {Γ : Context}
  {α β localState : Type}
  (update : ComponentUpdate Γ α localState)
  (f : α → β)
  : ComponentUpdate Γ β localState :=
  { update with value := f update.value }

def ComponentUpdate.mapLocals
  {Γ : Context}
  {α β γ : Type}
  (update : ComponentUpdate Γ α β)
  (f : β → γ)
  : ComponentUpdate Γ α γ :=
  { update with locals := f update.locals }

end Forms.Model
