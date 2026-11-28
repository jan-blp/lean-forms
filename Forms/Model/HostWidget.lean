module

public import Lean.Data.Json

@[expose] public section
namespace Forms.Model

/-- A control the host draws; only what `accept` returns reaches the model. -/
structure HostWidget (Input Output β : Type) where
  name : String
  [inputToJson : Lean.ToJson Input]
  [outputFromJson : Lean.FromJson Output]
  accept : Input → Output → Except String β

end Forms.Model
