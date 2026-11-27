module

public import Forms.Model.Component.Node

@[expose] public section
namespace Forms.Model

def CollectionDisplay.rename
  {Γ Δ : Context}
  {α β : Type}
  {views : Nat}
  (rename : Renaming Γ Δ)
  : CollectionDisplay Γ α β views → CollectionDisplay Δ α β views
  | .list => .list
  | .table headers rowLabel selected =>
    .table (headers.rename rename) (rowLabel.rename rename.liftRow)
      (selected.map (·.rename rename.liftRow))

def FieldEvidence.rename
  {Γ Δ : Context}
  {α β : Type}
  {target : Target Γ α β}
  (rename : Renaming Γ Δ)
  : FieldEvidence target → FieldEvidence (target.rename rename)
  | .none => .none
  | .recordedAt slot => .recordedAt slot

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
  | .field target label editor evidence =>
    .field (target.rename rename) (label.rename rename) editor (evidence.rename rename)
  | .computed label value => .computed (label.rename rename) (value.rename rename)
  | .button caption action => .button (caption.rename rename) (action.rename rename)
  | .tabBar label active tabs => .tabBar (label.rename rename) (rename active) (tabs.rename rename)
  | .withAvailability availability body =>
    .withAvailability (availability.rename rename) (body.rename rename)
  | .onChange update body => .onChange update (body.rename rename)
  | .select (decidableEq := _) (key := _) target label options selected availability =>
    .select (target.rename rename) (label.rename rename) (options.rename rename) selected
      (availability.rename rename)
  | .lookup (toJson := _) path label search availability =>
    .lookup path (label.rename rename) (search.rename rename) (availability.rename rename)
  | .output value => .output (value.rename rename)
  | .issues => .issues
  | .reports path => .reports path
  | .statusMarker reports => .statusMarker (reports.rename rename)
  | .collection path label row display =>
    .collection path (label.rename rename) (row.rename rename.liftRow) (display.rename rename)
  | .zoom? target body => .zoom? (target.rename rename) (body.rename rename)
  | .zoom path body => .zoom path (body.rename rename)
  | .load (inst := inst) source body =>
    .load (inst := inst) (source.rename rename) fun status => (body status).rename rename
  | .present body => .present (body.rename rename)

def PresentationNode.rename
  {Δ : ViewContext}
  {Γ Γ' : Context}
  {α state β : Type}
  {views : Nat}
  (rename : Renaming Γ Γ')
  (presentation : PresentationNode Δ Γ α state β views)
  : PresentationNode Δ Γ' α state β views :=
  match presentation with
  | .layout output arrangement => .layout (output.rename rename) (arrangement.rename rename)
  | .own component body => .own (component.rename rename) (body.rename rename.lift)
  | .bind initial body => .bind initial (body.rename rename.lift)

end

end Forms.Model
