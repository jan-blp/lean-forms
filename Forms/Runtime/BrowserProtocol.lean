module

public import Forms.Runtime.FormDefinition
public import Std.Data.HashMap

@[expose] public section
namespace Forms.Runtime.BrowserProtocol
open Lean

/-- Identifies a form instance within a store. -/
structure FormHandle where
  value : Nat
  deriving BEq, Hashable, Inhabited

/-- Holds the independent state of each open form in one Wasm instance.
Requests use handles to select a form; disposal removes its state. -/
structure Store where
  next : FormHandle := ⟨0⟩
  models : Std.HashMap FormHandle FormInstance := {}
  deriving Inhabited

def modelHandle (text : String) : Except String FormHandle := do
  let some value := text.toNat? | throw "Invalid form handle"
  pure ⟨value⟩

def execute (forms : Std.HashMap String RegisteredForm) (revision : String) (store : Store)
    (request : Wire.Request) : Except String (Store × Wire.Response) := do
  match request with
  | .open descriptor =>
    let some form := forms[descriptor.form]? | throw "Unknown compiled form"
    unless descriptor.revision == revision do
      throw "Compiled form version differs from the server. Rebuild Wasm, restart forms-web, then reload."
    let (state, snapshot) ← form.open descriptor.form descriptor.value
    let handle := store.next
    let store := { store with next := ⟨handle.value + 1⟩, models := store.models.insert handle state }
    pure (store, .opened (toString handle.value) snapshot)
  | .send text request =>
    let .ok handle := modelHandle text | throw "Invalid form handle"
    let some state := store.models[handle]? | throw "Unknown or disposed form handle"
    let (state, snapshot) ← state.execute request
    pure ({ store with models := store.models.insert handle state }, .updated snapshot)
  | .dispose text =>
    let .ok handle := modelHandle text | throw "Invalid form handle"
    unless store.models.contains handle do throw "Unknown or disposed form handle"
    pure ({ store with models := store.models.erase handle }, .disposed)

def respond (forms : Std.HashMap String RegisteredForm) (revision : String) (store : Store) (text : String) : Store × String :=
  let result : Except String (Store × Wire.Response) := match Json.parse text >>= fromJson? with
    | .error message => .error message
    | .ok request => execute forms revision store request
  match result with
  | .error error => (store, (toJson ({ ok := false, error } : Wire.Failure)).compress)
  | .ok (store, value) => (store, (toJson ({ ok := true, value } : Wire.Success)).compress)

end Forms.Runtime.BrowserProtocol
