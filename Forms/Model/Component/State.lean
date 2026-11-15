module

public import Forms.Model.Remote

@[expose] public section
namespace Forms.Model

/-- A single-entry cache of subtree state, keyed by the resolved load status. -/
structure LoadedState (data : Type) (state : Status data → Type) where
  status : Status data
  body : state status

/-- Looks up `status` in the single-entry cache, returning `initial` on a miss. -/
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

end Forms.Model
