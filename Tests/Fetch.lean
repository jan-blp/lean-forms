module

public import Forms.Runtime.ModelForm

public section
namespace Tests
open Forms.Model Forms.Runtime

def pendingFetch
  {Γ : Context}
  {α β : Type}
  {form : Component Γ α β}
  (state : ModelForm.State form)
  (request : HttpRequest)
  : IO HttpFetch := do
  let some (.loading generation) := state.cache[request]?
    | throw (IO.userError s!"FAIL request is not loading: {request.url}")
  return { request, generation }

/-- Loads `json` for `request` through the same queue and accept steps a host goes through. -/
def respond
  (state : FetchState)
  (request : HttpRequest)
  (json : Lean.Json)
  : FetchState :=
  let batch := (state.invalidate [.request request]).queue [request]
  batch.fetches.foldl (fun state fetch => (state.accept fetch (.ok json)).getD state) batch.state

end Tests
