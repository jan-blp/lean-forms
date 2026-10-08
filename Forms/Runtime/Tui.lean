import Forms.Runtime.JsonProtocol

namespace Forms.Runtime
open Composition

/-- The native interpreter owns interaction and returns the committed values. -/
class MonadTui (m : Type → Type) where
  runSpecification : String → m String

namespace Tui

def run {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] [MonadTui m]
    {context : DataType} (form : Component context) (value : ⟦context⟧) : m ⟦context⟧ := do
  let result ← MonadTui.runSpecification (JsonProtocol.encode form value)
  match Lean.Json.parse result >>= JsonProtocol.valueFromJson context with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

end Tui
end Forms.Runtime
