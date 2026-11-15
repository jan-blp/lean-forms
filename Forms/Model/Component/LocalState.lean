module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model

mutual
def ComponentNode.initialState
  {Γ : Context}
  {α state β : Type}
  {holes : Nat}
  (component : ComponentNode Γ α state β holes)
  : state :=
  match component with
  | .field .. => ()
  | .computed .. => ()
  | .button .. => ()
  | .tabBar .. => ()
  | .output .. => ()
  | .withAvailability _ body => body.initialState
  | .choiceOf (branches := branches) .. => branches.initialState
  | .list .. => []
  | .table .. => []
  | .focus _ body => body.initialState
  | .load (inst := _inst) (body := body) .. => ⟨.loading, (body .loading).initialState⟩
  | .present body => body.initialState

def PresentationNode.initialState
  {slots : List Nat}
  {Γ : Context}
  {α state β : Type}
  {views : Nat}
  (presentation : PresentationNode slots Γ α state β views)
  : state :=
  match presentation with
  | .layout .. => ()
  | .own component body => ⟨component.initialState, body.initialState⟩
  | .bind initial body => ⟨initial, body.initialState⟩

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
  {holes : Nat}
  (component : Component Γ α β holes)
  : component.LocalState :=
  component.node.initialState

end Forms.Model
