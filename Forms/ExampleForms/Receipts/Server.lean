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
  let ids := raw.receipts.map (·.id)
  let receipts ← raw.receipts.mapM fun receipt => do
    let owner ← state.claims.modifyGet fun claimed =>
      let owner := claimed.getD receipt.number receipt.id
      (owner, claimed.insert receipt.number owner)
    pure { receipt with alreadySubmitted := ⟨!ids.contains owner⟩ }
  pure { raw with receipts }

end Forms.ExampleForms
