module

public import Forms.Runtime.ModelView
public meta import Forms.Runtime.Display.Theorems

public section
namespace Forms.Runtime.ModelView

/-- No two controls `render` shows share a key, so a key names at most one control. -/
theorem render_keys_nodup
  {raw : Type}
  (component : Model.Component raw)
  (value : raw)
  (cache : Model.HttpRequest.Cache)
  (errors : List Feedback.Error)
  : ((render component value cache errors).controls.map (·.key)).Nodup :=
  Display.View.dedupe_keys_nodup _

end Forms.Runtime.ModelView
