import Forms.Runtime.JsonProtocol

namespace Forms.Runtime

/-- The native interpreter owns interaction and returns the committed values. -/
class MonadTui (m : Type → Type) where
  runSpecification : String → m String

namespace Tui

def run {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] [MonadTui m]
    {root : DataType} (form : Form root root) (value : DataType.denote root) : m (DataType.denote root) := do
  let result ← MonadTui.runSpecification (JsonProtocol.encode form value)
  match Lean.Json.parse result >>= JsonProtocol.valueFromJson root with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

end Tui
end Forms.Runtime
