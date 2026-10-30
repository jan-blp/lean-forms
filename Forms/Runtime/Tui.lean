import Forms.Runtime.CompositionProtocol
import Forms.Runtime.ActionHistoryProtocol

namespace Forms.Runtime

/-- The native interpreter owns interaction and returns submitted draft data or cancellation. -/
class MonadTui (m : Type → Type) where
  runSpecification : String → m String

namespace Tui

structure WidgetResult {ty : DataType} (refined : RefinedDataType ty) (action : Type) where
  value : RefinedDataType.ValidatedValue refined
  actions : Array (ActionInvocation ty action)

-- TODO: Return value and history from Tui.run for all components; remove runWidget.
def runWidget {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] [MonadTui m]
    {ty : DataType} (refined : RefinedDataType ty) (ids : Enum) (label : String)
    (actions : ids → WidgetAction ty) (draft : ⟦ty⟧)
    : m (Option (WidgetResult refined ids)) := do
  let component := Composition.Component.actionWidget (ids := ids) .self label actions
  let result ← MonadTui.runSpecification (CompositionProtocol.encode refined component draft)
  let decoded : Except String (Option (WidgetResult refined ids)) := do
    let json ← Lean.Json.parse result
    if json == .null then return none
    let history ← ActionHistoryProtocol.verify ids (fun id => (actions id).presentation) draft json
    let some value := RefinedDataType.validate refined history.value
      | throw "Invalid replayed value"
    return some { value, actions := history.actions }
  match decoded with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

def run {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] [MonadTui m]
    {root : DataType} (refined : RefinedDataType root) (component : Composition.Component root)
    (draft : ⟦root⟧) : m (Option (RefinedDataType.ValidatedValue refined)) := do
  if let .actionWidget (ids := ids) .self label actions := component then
    return (← runWidget refined ids label actions draft).map (·.value)
  let result ← MonadTui.runSpecification (CompositionProtocol.encode refined component draft)
  match Lean.Json.parse result >>= JsonProtocol.decodeResult refined with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

end Tui
end Forms.Runtime
