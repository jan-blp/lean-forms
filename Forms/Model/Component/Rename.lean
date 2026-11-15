module

public import Forms.Model.Component.Node

@[expose] public section
namespace Forms.Model

mutual
/-- Moves `component` into context `Δ`; binders keep their own entries in place. -/
def ComponentNode.rename
  {Γ Δ : Context}
  {α state β : Type}
  {holes : Nat}
  (rename : Renaming Γ Δ)
  (component : ComponentNode Γ α state β holes)
  : ComponentNode Δ α state β holes :=
  match component with
  | .field path label editor => .field path (label.rename rename) editor
  | .computed label value => .computed (label.rename rename) (value.rename rename)
  | .button caption action => .button (caption.rename rename) (action.rename rename)
  | .tabBar label active tabs => .tabBar (label.rename rename) (rename active) (tabs.rename rename)
  | .withAvailability availability body =>
    .withAvailability (availability.rename rename) (body.rename rename)
  | .select (decidableEq := _) (key := _) path label options selected =>
    .select path (label.rename rename) (options.rename rename) selected
  | .output value => .output (value.rename rename)
  | .list path label row => .list path (label.rename rename) (row.rename rename.liftRow)
  | .table path label headers rowLabel row selection =>
    .table path (label.rename rename) (headers.rename rename) (rowLabel.rename rename.liftRow)
      (row.rename rename.liftRow) (selection.map rename)
  | .focus target body => .focus (target.rename rename) (body.rename rename)
  | .load (inst := inst) source body =>
    .load (inst := inst) (source.rename rename) fun status => (body status).rename rename
  | .present body => .present (body.rename rename)

def PresentationNode.rename
  {slots : List Nat}
  {Γ Δ : Context}
  {α state β : Type}
  {views : Nat}
  (rename : Renaming Γ Δ)
  (presentation : PresentationNode slots Γ α state β views)
  : PresentationNode slots Δ α state β views :=
  match presentation with
  | .layout output arrangement => .layout (output.rename rename) (arrangement.rename rename)
  | .own component body => .own (component.rename rename) (body.rename rename.lift)
  | .bind initial body => .bind initial (body.rename rename.lift)

end

end Forms.Model
