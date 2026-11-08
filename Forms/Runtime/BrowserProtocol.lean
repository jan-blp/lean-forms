module

public import Forms.Runtime.PersonProtocol

@[expose] public section
namespace Forms.Runtime.BrowserProtocol
open Lean

structure Store where
  next : Nat := 0
  models : List (Nat × PersonProtocol.State) := []
  deriving Inhabited

def modelHandle (text : String) : Except String Nat := do
  let some value := text.toNat? | throw "Invalid form handle"
  pure value

def execute (revision : String) (store : Store) (json : Json) : Except String (Store × Wire.Response) := do
  match ← (fromJson? json : Except String Wire.Request) with
  | .open descriptor =>
    unless descriptor.form == PersonProtocol.name do throw "Unknown compiled form"
    unless descriptor.revision == revision do
      throw "Compiled form version differs from the server. Rebuild Wasm and reload."
    let initial ← fromJson? descriptor.value
    let state := ModelForm.openState initial
    let handle := store.next
    let store := { store with next := handle + 1, models := (handle, state) :: store.models }
    pure (store, .opened (toString handle) (PersonProtocol.snapshot state))
  | .send text request =>
    let handle ← modelHandle text
    let some (_, state) := store.models.find? (·.1 == handle) | throw "Unknown or disposed form handle"
    let (state, snapshot) ← PersonProtocol.execute state request
    pure ({ store with models := store.models.map fun (key, current) =>
      (key, if key == handle then state else current) }, .updated snapshot)
  | .dispose text =>
    let handle ← modelHandle text
    unless store.models.any (·.1 == handle) do throw "Unknown or disposed form handle"
    pure ({ store with models := store.models.filter (·.1 != handle) }, .disposed)

def respond (revision : String) (store : Store) (text : String) : Store × String :=
  match Json.parse text >>= execute revision store with
  | .error error => (store, (toJson ({ ok := false, error } : Wire.Failure)).compress)
  | .ok (store, value) => (store, (toJson ({ ok := true, value } : Wire.Success)).compress)

end Forms.Runtime.BrowserProtocol
