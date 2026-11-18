module

public import Forms.ExampleForms.Receipts
public import Std.Data.HashMap

@[expose] public section
namespace Forms.ExampleForms
open Forms.Model

def Receipts.serverCheck
  (claims : IO.Ref (Std.HashMap String Uuid))
  (raw : Receipts.Raw)
  : IO Receipts.Raw := do
  let ids := raw.receipts.map (·.id)
  let receipts ← raw.receipts.mapM fun receipt => do
    let owner ← claims.modifyGet fun claimed =>
      let owner := claimed.getD receipt.number receipt.id
      (owner, claimed.insert receipt.number owner)
    pure { receipt with alreadySubmitted := ⟨!ids.contains owner⟩ }
  pure { raw with receipts }

end Forms.ExampleForms
