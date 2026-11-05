module

public import Forms.Runtime.CompositionProtocol
public import Forms.Runtime.ComponentHistoryProtocol

@[expose] public section

namespace Forms.Runtime

class MonadTui (m : Type → Type) where
  runSpecification : String → m String

namespace Tui

structure ComponentResult {ty : DataType}
  (refined : RefinedDataType ty)
  (component : Composition.Component ty) where
  value : RefinedDataType.ValidatedValue refined
  actions : Array component.Invocation

def run {m : Type → Type}
  [Monad m]
  [MonadExceptOf IO.Error m]
  [MonadTui m]
  {ty : DataType}
  (refined : RefinedDataType ty)
  (component : Composition.Component ty)
  (draft : ⟦ty⟧)
  : m (Option (ComponentResult refined component)) := do
  let result ← MonadTui.runSpecification (CompositionProtocol.encode refined component draft)
  let decoded : Except String (Option (ComponentResult refined component)) := do
    let json ← Lean.Json.parse result
    if json == .null then return none
    let history ← (ComponentHistoryProtocol.verify component draft json).mapError toString
    let some value := RefinedDataType.validate refined history.value
      | throw "Invalid replayed value"
    return some { value, actions := history.actions }
  match decoded with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

end Tui
end Forms.Runtime
