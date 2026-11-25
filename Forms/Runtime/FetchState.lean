module

public import Forms.Model.Remote

public section
namespace Forms.Runtime

structure FetchState where
  private mk ::
  private responses : Model.HttpRequest.Cache
  private nextGeneration : Nat

namespace FetchState

def empty : FetchState :=
  { responses := {}, nextGeneration := 0 }

instance : EmptyCollection FetchState where
  emptyCollection := empty

def cache (state : FetchState) : Model.HttpRequest.Cache := state.responses

structure Queued where
  state : FetchState
  fetches : List Model.HttpFetch

def queue
  (state : FetchState)
  (requests : List Model.HttpRequest)
  : Queued :=
  let missing := requests.filter (!state.responses.contains ·) |>.eraseDups
  if missing.isEmpty then { state, fetches := [] } else
    { state := {
        responses := missing.foldl
          (fun cache request => cache.insert request (.loading state.nextGeneration))
          state.responses
        nextGeneration := state.nextGeneration + 1 }
      fetches := missing.map fun request =>
        { request, generation := state.nextGeneration } }

def invalidate
  (state : FetchState)
  (scopes : List Model.RequestScope)
  : FetchState :=
  if scopes.isEmpty then state else
    { state with responses := state.responses.filter fun request _ =>
        !scopes.any (·.contains request) }

/-- Drops failed responses so that they are fetched again. -/
def retryFailed (state : FetchState) : FetchState :=
  { state with responses := state.responses.filter fun _ response => match response with
      | .failed _ => false
      | .loading _ => true
      | .loaded _ => true }

def accept
  (state : FetchState)
  (fetch : Model.HttpFetch)
  (response : Except String Lean.Json)
  : Option FetchState :=
  match state.responses[fetch.request]? with
  | some (.loading generation) =>
    if generation != fetch.generation then none else
      let cached := match response with
        | .ok json => .loaded json
        | .error message => .failed message
      some { state with responses := state.responses.insert fetch.request cached }
  | none
  | some (.loaded _)
  | some (.failed _) => none

theorem accept_stale
  (state : FetchState)
  (fetch : Model.HttpFetch)
  (response : Except String Lean.Json)
  (generation : Nat)
  (pending : state.cache[fetch.request]? = some (.loading generation))
  (stale : generation ≠ fetch.generation)
  : state.accept fetch response = none := by
  simp [accept, cache] at pending ⊢
  simp [pending, stale]

end FetchState
end Forms.Runtime
