module

public import Forms.ExampleForms.Registry
public import Forms.ExampleForms.Presentation
public import Forms.Model.Component.Rename

public section
namespace Tests.Rename
open Forms.Model Forms.Runtime Forms.Runtime.ModelView Forms.ExampleForms

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

private def argument : Display.Editor → Option Input
  | .text _ => some (.text "x")
  | .natural _ => some (.text "1")
  | .checkbox value => some (.boolean !value)
  | .choice selected _ => some (.text selected)
  | .action => none
  | .tabs active labels => some (.text (toString ((active + 1) % labels.length.max 1)))

/-- A weakened component renders, outputs and reacts to every control like the original. -/
private def weakeningPreserves
  {α β : Type}
  [BEq α]
  [BEq β]
  (name : String)
  (component : Component [] α β)
  (value : α)
  : IO Unit := do
  let weakened : Component [⟨.readOnly, Unit⟩] α β := component.weaken
  let original := component.evaluate value Env.nil
  let shifted := weakened.evaluate value env[()]
  check s!"{name}WeakenedRendersTheSame"
    (original.view == shifted.view && original.output == shifted.output)
  let mut same := true
  for control in original.view.controls do
    let input := argument control.input
    match original.applyKey control.key input, shifted.applyKey control.key input with
    | .ok first, .ok second =>
      let first := component.evaluate first.value first.state {} first.locals
      let second := weakened.evaluate second.value second.state {} second.locals
      same := same && first.value == second.value && first.view == second.view &&
        first.output == second.output
    | .error _, .error _ => pure ()
    | _, _ => same := false
  check s!"{name}WeakenedReactsTheSame" same

def run : IO Unit := do
  weakeningPreserves "SharedState" SharedState.form SharedState.initial
  weakeningPreserves "Outputs" Outputs.nested Outputs.initial
  weakeningPreserves "Selection" Outputs.selectedDescriptions ["same", "same", "other"]
  weakeningPreserves "Tabs" Presentation.sharedTabs 0
  weakeningPreserves "Notes" Presentation.notes ["a", "b"]

end Tests.Rename
