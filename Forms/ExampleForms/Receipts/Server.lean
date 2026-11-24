module

public import Forms.ExampleForms.Receipts
public import Std.Data.HashMap

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

structure Receipts.ServerState where
  claims : IO.Ref (Std.HashMap String Uuid)

def Receipts.ServerState.init : IO Receipts.ServerState := do
  return { claims := ← IO.mkRef {} }

def Receipts.serverCheck
  (state : Receipts.ServerState)
  (raw : Receipts.Raw)
  : IO Receipts.Raw := do
  for entry in raw.receipts.entries do
    state.claims.modify fun claimed =>
      claimed.insert entry.value.number (claimed.getD entry.value.number entry.id)
  let claimed ← state.claims.get
  let ids := raw.receipts.ids
  let receipts := raw.receipts.mapWithId fun id receipt =>
    { receipt with alreadySubmitted := ⟨!ids.contains (claimed.getD receipt.number id)⟩ }
  pure { raw with receipts }

end Forms.ExampleForms
