module

public import Forms.Model.Component.Node

@[expose] public section
namespace Forms.Model

mutual
/-- Moves `component` into context `Δ`; binders keep their own entries in place. -/
def ComponentNode.rename
  {Γ Δ : Context}
  {α state β : Type}
  (rename : Renaming Γ Δ)
  (component : ComponentNode Γ α state β)
  : ComponentNode Δ α state β :=
  match component with
  | .field path label editor => .field path (label.rename rename) editor
  | .computed label value => .computed label (value.rename rename)
  | .button caption action => .button (caption.rename rename) (action.rename rename)
  | .tabBar label active tabs => .tabBar label (rename active) (tabs.rename rename)
  | .withAvailability availability body =>
    .withAvailability (availability.rename rename) (body.rename rename)
  | .choiceOf path label branches => .choiceOf path label (branches.rename rename)
  | .output value => .output (value.rename rename)
  | .sequence first second => .sequence (first.rename rename) (second.rename rename)
  | .bind initial body => .bind initial (body.rename rename.lift)
  | .observe producer body => .observe (producer.rename rename) (body.rename rename.lift)
  | .list path label itemLabel initial body =>
    .list path label itemLabel initial (body.rename rename)
  | .table path label itemLabel initial columns selection =>
    .table path label itemLabel initial (columns.rename rename) (selection.map rename)
  | .focus target body => .focus (target.rename rename) (body.rename rename)
  | .load (inst := inst) source body =>
    .load (inst := inst) (source.rename rename) fun status => (body status).rename rename
  | .present body => .present (body.rename rename)

def PresentationNode.rename
  {slots : Nat}
  {Γ Δ : Context}
  {α state β : Type}
  (rename : Renaming Γ Δ)
  (presentation : PresentationNode slots Γ α state β)
  : PresentationNode slots Δ α state β :=
  match presentation with
  | .layout output arrangement => .layout (output.rename rename) (arrangement.rename rename)
  | .own component body => .own (component.rename rename) (body.rename rename.lift)
  | .bind initial body => .bind initial (body.rename rename.lift)

def ColumnsNode.rename
  {headers : List String}
  {Γ Δ : Context}
  {α state β : Type}
  (rename : Renaming Γ Δ)
  (columns : ColumnsNode headers Γ α state β)
  : ColumnsNode headers Δ α state β :=
  match columns with
  | .output value => .output (value.rename rename)
  | .cons header cell rest => .cons header (cell.rename rename) (rest.rename rename)
  | .observe header cell rest => .observe header (cell.rename rename) (rest.rename rename.lift)
  | .bind initial body => .bind initial (body.rename rename.lift)
  | .focus target body => .focus (target.rename rename) (body.rename rename)

def BranchNode.rename
  {Γ Δ : Context}
  {α state : Type}
  (rename : Renaming Γ Δ)
  (branch : BranchNode Γ α state)
  : BranchNode Δ α state :=
  match branch with
  | .mk key label inject project initial body =>
    .mk key label inject project initial (body.rename rename)

def BranchesNode.rename
  {Γ Δ : Context}
  {α state : Type}
  (rename : Renaming Γ Δ)
  (branches : BranchesNode Γ α state)
  : BranchesNode Δ α state :=
  match branches with
  | .nil => .nil
  | .cons head tail => .cons (head.rename rename) (tail.rename rename)
end

end Forms.Model
