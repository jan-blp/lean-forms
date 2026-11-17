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
  | .issues => ()
  | .withAvailability _ body => body.initialState
  | .select (decidableEq := _) (key := _) .. => ()
  | .collection (hasUuid := _) .. => []
  | .focus _ body => body.initialState
  | .zoom _ body => body.initialState
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

end

@[reducible] def Component.initialState
  {Γ : Context}
  {α β : Type}
  {holes : Nat}
  (component : Component Γ α β holes)
  : component.LocalState :=
  component.node.initialState

end Forms.Model
