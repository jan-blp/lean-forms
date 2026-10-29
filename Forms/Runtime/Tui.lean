import Forms.Runtime.CompositionProtocol

namespace Forms.Runtime

/-- The native interpreter owns interaction and returns submitted draft data or cancellation. -/
class MonadTui (m : Type → Type) where
  runSpecification : String → m String

namespace Tui

def run {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] [MonadTui m]
    {root : DataType} (refined : RefinedDataType root) (component : Composition.Component root)
    (draft : ⟦root⟧) : m (Option (RefinedDataType.ValidatedValue refined)) := do
  let result ← MonadTui.runSpecification (CompositionProtocol.encode refined component draft)
  match Lean.Json.parse result >>= JsonProtocol.decodeResult refined with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

end Tui
end Forms.Runtime
