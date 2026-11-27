module

public import Forms.Model.Remote
public import Forms.Model.ErasedLocation

@[expose] public section
namespace Forms.Model

/-- A single-entry cache of subtree state, keyed by the resolved load status. -/
structure LoadedState (data : Type) (state : Status data → Type) where
  status : Status data
  body : state status

def LoadedState.at
  {data : Type}
  [DecidableEq data]
  {state : Status data → Type}
  (stored : LoadedState data state)
  (status : Status data)
  (initial : state status)
  : state status :=
  if same : stored.status = status then same ▸ stored.body else initial

structure ObservationState (producer consumers : Type) where
  producer : producer
  consumers : consumers

/-- Ignored unless `epoch` is the current input and the `onChange` node is still at `location`. -/
structure PendingReaction (α : Type) where
  old : α
  epoch : Nat
  location : ErasedLocation

/-- `results` answer the action's earlier calls; the action is replayed with them. -/
structure PendingCall where
  id : Uuid
  location : ErasedLocation
  results : List (Except String Lean.Json)

structure ReactionCall (α : Type) where
  old : α
  new : α
  call : PendingCall

structure ReactionState (α state : Type) where
  pending : Option (PendingReaction α)
  call : Option (ReactionCall α)
  body : state

end Forms.Model
