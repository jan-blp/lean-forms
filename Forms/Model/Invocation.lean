module

public import Forms.Model.Context
public import Forms.Model.Diagnostic
public import Forms.Model.Supply

@[expose] public section
namespace Forms.Model

inductive InvocationError where
  | hidden
  | disabled
  /-- No control with the key is shown. -/
  | absent
  /-- No option of the select has the requested key. -/
  | unavailableBranch (key : String)
  deriving DecidableEq, Repr

instance : ToString InvocationError where
  toString
    | .hidden => "This action is unavailable: the control is hidden."
    | .disabled => "This action is unavailable: the control is disabled."
    | .absent => "This action is unavailable: the control is no longer shown."
    | .unavailableBranch key => s!"This action is unavailable: branch '{key}' is no longer available."

structure ComponentUpdate (Γ : Context) (α localState : Type) where
  value : α
  state : Env Γ
  locals : localState
  visit : Option Destination := none

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
