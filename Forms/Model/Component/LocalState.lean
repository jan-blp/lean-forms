module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model

mutual
def ComponentNode.initialState
  {Γ : Context}
  {α state β : Type}
  (component : ComponentNode Γ α state β)
  : state :=
  match component with
  | .field .. => ()
  | .computed .. => ()
  | .button .. => ()
  | .tabBar .. => ()
  | .output .. => ()
  | .withAvailability _ body => body.initialState
  | .choiceOf _ _ branches => branches.initialState
  | .list .. => []
  | .table .. => []
  | .focus _ body => body.initialState
  | .load (inst := _inst) (body := body) .. => ⟨.loading, (body .loading).initialState⟩
  | .present body => body.initialState

def PresentationNode.initialState
  {slots : Nat}
  {Γ : Context}
  {α state β : Type}
  (presentation : PresentationNode slots Γ α state β)
  : state :=
  match presentation with
  | .layout .. => ()
  | .own component body => ⟨component.initialState, body.initialState⟩
  | .bind initial body => ⟨initial, body.initialState⟩

def ColumnsNode.initialState
  {headers : List String}
  {Γ : Context}
  {α state β : Type}
  (columns : ColumnsNode headers Γ α state β)
  : state :=
  match columns with
  | .output .. => ()
  | .cons _ cell rest => ⟨cell.initialState, rest.initialState⟩
  | .observe _ cell rest => ⟨cell.initialState, rest.initialState⟩
  | .bind initial body => ⟨initial, body.initialState⟩
  | .focus _ body => body.initialState

def BranchNode.initialState
  {Γ : Context}
  {α state : Type}
  (branch : BranchNode Γ α state)
  : state :=
  match branch with
  | .mk (body := body) .. => body.initialState

def BranchesNode.initialState
  {Γ : Context}
  {α state : Type}
  (branches : BranchesNode Γ α state)
  : state :=
  match branches with
  | .nil => ()
  | .cons head tail => ⟨head.initialState, tail.initialState⟩
end

@[reducible] def Component.initialState
  {Γ : Context}
  {α β : Type}
  (component : Component Γ α β)
  : component.LocalState :=
  component.node.initialState

@[reducible] def Columns.initialState
  {Γ : Context}
  {α β : Type}
  (columns : Columns Γ α β)
  : columns.LocalState :=
  columns.node.initialState

end Forms.Model
