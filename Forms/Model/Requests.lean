module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model

mutual
/-- Requests read from the current model, UI state, and loaded responses. -/
def Component.requests {raw : Type} (component : Component raw) (cache : HttpRequest.Cache)
    (current : raw) (state : UiState := {}) : List HttpRequest :=
  match component with
  | .field .. => []
  | .groupOf _ children => children.requests cache current state
  | .computed .. => []
  | .withAvailability availability body =>
    match availability.eval current state with
    | .hidden => []
    | _ => body.requests cache current state
  | .choiceOf path _ branches => branches.requests cache (path.get current) state
  | .list path _ _ _ body =>
    (path.get current).flatMap fun item => body.requests cache item state
  | .table path _ _ _ columns _ =>
    (path.get current).flatMap fun item => columns.requests cache item state
  | .focus target body =>
    ((target.eval current state).get? current).toList.flatMap fun value => body.requests cache value state
  | .load source body =>
    let source := source.eval current state
    source.request?.toList ++ (body (source.resolve cache)).requests cache current state

def Components.requests {raw : Type} (children : Components raw) (cache : HttpRequest.Cache)
    (current : raw) (state : UiState := {}) : List HttpRequest :=
  match children with
  | .nil => []
  | .cons head tail => head.requests cache current state ++ tail.requests cache current state

def Columns.requests {raw : Type} (columns : Columns raw) (cache : HttpRequest.Cache)
    (current : raw) (state : UiState := {}) : List HttpRequest :=
  match columns with
  | .nil => []
  | .cons _ head tail => head.requests cache current state ++ tail.requests cache current state

def Branch.requests {sum : Type} (branch : Branch sum) (cache : HttpRequest.Cache)
    (current : sum) (state : UiState := {}) : List HttpRequest :=
  match branch with
  | .mk _ _ _ project _ body =>
    match project current with
    | some payload => body.requests cache payload state
    | none => []

def Branches.requests {sum : Type} (branches : Branches sum) (cache : HttpRequest.Cache)
    (current : sum) (state : UiState := {}) : List HttpRequest :=
  match branches with
  | .nil => []
  | .cons head tail => head.requests cache current state ++ tail.requests cache current state
end

end Forms.Model
