import Forms.Runtime.JsonProtocol

namespace Forms.Runtime

/-- The native interpreter owns interaction and returns submitted draft data or cancellation. -/
class MonadTui (m : Type → Type) where
  runSpecification : String → m String

namespace Tui

def run {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] [MonadTui m]
    {root : DataType} (refined : RefinedDataType root) (form : Form root root) (draft : DataType.denote root)
    : m (Option refined.denote) := do
  let result ← MonadTui.runSpecification (JsonProtocol.encode refined form draft)
  match Lean.Json.parse result >>= JsonProtocol.decodeResult refined with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

end Tui
end Forms.Runtime
