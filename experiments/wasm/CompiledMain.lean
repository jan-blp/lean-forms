module

public import Forms.Runtime.CompiledForms

public section

namespace FormsBrowser
open Lean Forms.Runtime

initialize formStore : IO.Ref CompiledForms.Store ← IO.mkRef {}

@[export forms_handle_request]
def request (text : String) : IO String := do
  let store ← formStore.get
  let result := do
    let request ← Json.parse text
    CompiledForms.execute store request
  match result with
  | .error error => return (Json.mkObj [("ok", toJson false), ("error", toJson error)]).compress
  | .ok (store, value) =>
    formStore.set store
    return (Json.mkObj [("ok", toJson true), ("value", value)]).compress

end FormsBrowser
