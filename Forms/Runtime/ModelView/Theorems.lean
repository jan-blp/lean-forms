module

public import Forms.Runtime.ModelView
public meta import Forms.Runtime.Display.Theorems

public section
namespace Forms.Runtime.ModelView

/-- No two controls `render` shows share a key, so a key names at most one control. -/
theorem render_keys_nodup
  {Γ : Model.Context}
  {α β : Type}
  (component : Model.Component Γ α β)
  (value : α)
  (fetchState : FetchState)
  (errors : List Model.Diagnostic)
  (state : Model.Env Γ)
  : ((render component value fetchState errors state).controls.map (·.key)).Nodup := by
  unfold render evaluate
  exact Display.View.dedupe_keys_nodup _

end Forms.Runtime.ModelView
