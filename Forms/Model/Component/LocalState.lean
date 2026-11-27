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
  | .reports .. => ()
  | .statusMarker .. => ()
  | .withAvailability _ body => body.initialState
  | .onChange _ body => { pending := none, body := body.initialState }
  | .select (decidableEq := _) (key := _) .. => ()
  | .lookup (toJson := _) .. => none
  | .collection .. => {}
  | .zoom? _ body => body.initialState
  | .zoom _ body => body.initialState
  | .load (inst := _inst) (body := body) .. => ⟨.loading, (body .loading).initialState⟩
  | .present body => body.initialState

def PresentationNode.initialState
  {Δ : ViewContext}
  {Γ : Context}
  {α state β : Type}
  {views : Nat}
  (presentation : PresentationNode Δ Γ α state β views)
  : state :=
  match presentation with
  | .layout .. => ()
  | .own component body => ⟨component.initialState, body.initialState⟩
  | .bind initial body => ⟨initial, body.initialState⟩

end

mutual
def ComponentNode.dropReactions
  {Γ : Context}
  {α state β : Type}
  {holes : Nat}
  (component : ComponentNode Γ α state β holes)
  (locals : state)
  : state :=
  match component with
  | .field .. => locals
  | .computed .. => locals
  | .button .. => locals
  | .tabBar .. => locals
  | .output .. => locals
  | .issues => locals
  | .reports .. => locals
  | .statusMarker .. => locals
  | .withAvailability _ body => body.dropReactions locals
  | .onChange _ body => { pending := none, body := body.dropReactions locals.body }
  | .select (decidableEq := _) (key := _) .. => locals
  | .lookup (toJson := _) .. => locals
  | .collection (row := row) .. => locals.map fun _ rowLocals => row.dropReactions rowLocals
  | .zoom? _ body => body.dropReactions locals
  | .zoom _ body => body.dropReactions locals
  | .load (inst := _inst) (body := body) .. =>
    { status := locals.status, body := (body locals.status).dropReactions locals.body }
  | .present body => body.dropReactions locals

def PresentationNode.dropReactions
  {Δ : ViewContext}
  {Γ : Context}
  {α state β : Type}
  {views : Nat}
  (presentation : PresentationNode Δ Γ α state β views)
  (locals : state)
  : state :=
  match presentation with
  | .layout .. => locals
  | .own component body =>
    { producer := component.dropReactions locals.producer
      consumers := body.dropReactions locals.consumers }
  | .bind _ body => { value := locals.value, tail := body.dropReactions locals.tail }

end

abbrev Component.initialState
  {Γ : Context}
  {α β : Type}
  {holes : Nat}
  (component : Component Γ α β holes)
  : component.LocalState :=
  component.node.initialState

end Forms.Model
