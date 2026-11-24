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

end Tests
