module

public import Forms.ExampleForms.FormFingerprint

public section

namespace FormsBrowser
open Lean Forms.Runtime

initialize formStore : IO.Ref BrowserProtocol.Store ← IO.mkRef BrowserProtocol.Store.empty

@[export forms_handle_request]
def request (text : String) : IO String := do
  let (store, response) := BrowserProtocol.respond Forms.ExampleForms.registeredForms Forms.ExampleForms.formFingerprint (← formStore.get) text
  formStore.set store
  return response

end FormsBrowser
