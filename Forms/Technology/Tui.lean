import Forms.Technology.Specification

namespace Forms.Technology

/-- The native interpreter owns interaction and returns the committed values. -/
class MonadTui (m : Type → Type) where
  runSpecification : String → m String

namespace Tui

def run {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] [MonadTui m]
    {root : Ty} (form : Form root root) (value : Ty.denote root) : m (Ty.denote root) := do
  let result ← MonadTui.runSpecification (Specification.encode form value)
  match Lean.Json.parse result >>= Specification.valueFromJson root with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

end Tui
end Forms.Technology
