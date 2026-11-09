module

public import Forms.Runtime.CompiledRevision

public section

namespace FormsBrowser
open Lean Forms.Runtime

initialize formStore : IO.Ref BrowserProtocol.Store ← IO.mkRef {}

@[export forms_handle_request]
def request (text : String) : IO String := do
  let (store, response) := BrowserProtocol.respond Forms.ExampleForms.registeredForms compiledRevision (← formStore.get) text
  formStore.set store
  return response

end FormsBrowser
