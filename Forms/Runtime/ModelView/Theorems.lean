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

attribute [local simp] StateT.run bind StateT.bind Except.bind pure StateT.pure Except.pure throw
  throwThe MonadExcept.throw MonadExceptOf.throw StateT.lift StateT.instMonadExceptOf
  instMonadExceptOfExcept Except.mapError MonadExcept.ofExcept in
theorem hostWidget_writes_accepted
    {Γ : Model.Context}
    {α β Input Output : Type}
    {contract : Model.HostWidget Input Output β}
    {written : Model.Target Γ α β}
    {label : Model.Computation Γ α String}
    {input : Model.Computation Γ α Input}
    {value : α}
    {env : Model.Env Γ}
    {ambient : Ambient}
    {target : Display.Target}
    {location : Model.ErasedLocation}
    {disabled : Bool}
    {trigger : Trigger}
    {supply supply' : Model.Supply}
    {updated : Model.ComponentUpdate Γ α Unit}
    (applied : ((evaluateNode (.hostWidget contract written label input) value env ambient () target
      location disabled).apply [] trigger).run supply = .ok (updated, supply'))
    : ∃ output stored, contract.accept (input.eval value env) output = .ok stored ∧
      updated = written.set stored value env := by
  simp only [evaluateNode] at applied
  cases disabled
  · cases trigger with
    | input argument epoch =>
      rcases argument with _ | ⟨_ | _ | _ | _ | _ | sent⟩ <;>
        simp [Trigger.argument] at applied
      rcases decoded : contract.outputFromJson.fromJson? sent with _ | output <;>
        simp [decoded] at applied
      rcases accepted : contract.accept (input.eval value env) output with _ | stored <;>
        simp [accepted, StateT.pure] at applied
      exact ⟨output, stored, accepted, applied.1.symm⟩
    | react => simp [Trigger.argument, absent] at applied
    | resume id result => simp [Trigger.argument, absent] at applied
  · simp at applied

end Forms.Runtime.ModelView
