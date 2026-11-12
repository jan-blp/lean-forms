module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model

mutual
/-- The requests whose responses `component` reads in `current`; hidden parts read none. -/
def Component.requests {raw : Type} : Component raw → HttpRequest.Cache → raw → List HttpRequest
  | .field .., _, _ => []
  | .groupOf _ children, cache, current => children.requests cache current
  | .computed .., _, _ => []
  | .withAvailability availability body, cache, current =>
    match availability.eval current with
    | .enabled => body.requests cache current
    | .hidden => []
    | .disabled => body.requests cache current
  | .choiceOf path _ branches, cache, current => branches.requests cache (path.get current)
  | .list path _ _ _ body, cache, current =>
    (path.get current).flatMap fun item => body.requests cache item
  | .table path _ _ _ columns, cache, current =>
    (path.get current).flatMap fun item => columns.requests cache item
  | .load source body, cache, current =>
    let source := source.eval current
    source.request?.toList ++ (body (source.resolve cache)).requests cache current

def Components.requests {raw : Type} : Components raw → HttpRequest.Cache → raw → List HttpRequest
  | .nil, _, _ => []
  | .cons head tail, cache, current =>
    head.requests cache current ++ tail.requests cache current

def Columns.requests {raw : Type} : Columns raw → HttpRequest.Cache → raw → List HttpRequest
  | .nil, _, _ => []
  | .cons _ head tail, cache, current =>
    head.requests cache current ++ tail.requests cache current

def Branch.requests {sum : Type} : Branch sum → HttpRequest.Cache → sum → List HttpRequest
  | .mk _ _ _ project _ body, cache, current =>
    match project current with
    | some payload => body.requests cache payload
    | none => []

def Branches.requests {sum : Type} : Branches sum → HttpRequest.Cache → sum → List HttpRequest
  | .nil, _, _ => []
  | .cons head tail, cache, current =>
    head.requests cache current ++ tail.requests cache current
end

end Forms.Model
