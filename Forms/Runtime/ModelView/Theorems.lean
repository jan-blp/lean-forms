module

public import Forms.Runtime.ModelView
public meta import Forms.Runtime.Display.Theorems

public section
namespace Forms.Runtime.ModelView

/-- No two controls `render` shows share a key, so a key names at most one control. -/
theorem render_keys_nodup
  {Γ : List Type}
  {raw : Type}
  (component : Model.Component Γ raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  (state : Model.Env Γ)
  : ((render component value cache errors state).controls.map (·.key)).Nodup :=
  Display.View.dedupe_keys_nodup _

end Forms.Runtime.ModelView
