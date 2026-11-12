module

public import Forms.Model.Component.LocalState

@[expose] public section
namespace Forms.Model

mutual
/-- Requests read from the current model, UI state, and loaded responses. -/
def Component.requests {Γ : Context} {raw : Type} (component : Component Γ raw) (cache : HttpRequest.Cache)
    (current : raw) (state : Env Γ) (locals : component.LocalState := component.initialState) : List HttpRequest :=
  match component with
  | .field .. => []
  | .groupOf _ children => children.requests cache current state locals
  | .computed .. => []
  | .withAvailability availability body =>
    match availability.eval current state with
    | .hidden => []
    | _ => body.requests cache current state locals
  | .choiceOf path _ branches => branches.requests cache (path.get current) state locals
  | .list path _ _ _ body =>
    (path.get current).zipIdx |>.flatMap fun (item, index) =>
      body.requests cache item state (locals[index]?.getD body.initialState)
  | .table path _ _ _ columns _ =>
    (path.get current).zipIdx |>.flatMap fun (item, index) =>
      columns.requests cache item state (locals[index]?.getD columns.initialState)
  | .focus target body =>
    ((target.eval current state).get? current).toList.flatMap fun value => body.requests cache value state locals
  | .bind _ body => body.requests cache current (Env.cons locals.value state) locals.tail
  | @Component.load _ _ _ _inst source body =>
    let source := source.eval current state
    let status := source.resolve cache
    source.request?.toList ++ (body status).requests cache current state (locals.at status (body status).initialState)

def Components.requests {Γ : Context} {raw : Type} (children : Components Γ raw) (cache : HttpRequest.Cache)
    (current : raw) (state : Env Γ) (locals : children.LocalState := children.initialState) : List HttpRequest :=
  match children with
  | .nil => []
  | .cons head tail => head.requests cache current state locals.value ++ tail.requests cache current state locals.tail

def Columns.requests {Γ : Context} {raw : Type} (columns : Columns Γ raw) (cache : HttpRequest.Cache)
    (current : raw) (state : Env Γ) (locals : columns.LocalState := columns.initialState) : List HttpRequest :=
  match columns with
  | .nil => []
  | .cons _ head tail => head.requests cache current state locals.value ++ tail.requests cache current state locals.tail

def Branch.requests {Γ : Context} {sum : Type} (branch : Branch Γ sum) (cache : HttpRequest.Cache)
    (current : sum) (state : Env Γ) (locals : branch.LocalState := branch.initialState) : List HttpRequest :=
  match branch with
  | .mk _ _ _ project _ body =>
    match project current with
    | some payload => body.requests cache payload state locals
    | none => []

def Branches.requests {Γ : Context} {sum : Type} (branches : Branches Γ sum) (cache : HttpRequest.Cache)
    (current : sum) (state : Env Γ) (locals : branches.LocalState := branches.initialState) : List HttpRequest :=
  match branches with
  | .nil => []
  | .cons head tail => head.requests cache current state locals.value ++ tail.requests cache current state locals.tail
end

end Forms.Model
