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
  | .visibleWhen condition body, cache, current =>
    if condition.eval current then body.requests cache current else []
  | .disabledWhen _ body, cache, current => body.requests cache current
  | .choiceOf path _ branches, cache, current => branches.requests cache (path.get current)
  | .list path _ _ _ body, cache, current =>
    (path.get current).flatMap fun item => body.requests cache item
  | .load source body, cache, current =>
    let source := source.eval current
    source.request?.toList ++ match source.resolve cache with
      | .ready data => body.requests cache ⟨data, current⟩
      | .loading => []
      | .failed _ => []
  | .keyedChoice (keyEq := _) (keyHash := _) (path := path) (body := body) .., cache, current =>
    match (path.get current).selected with
    | some (picked, payload) => body.requests cache ⟨picked, payload⟩
    | none => []

def Components.requests {raw : Type} : Components raw → HttpRequest.Cache → raw → List HttpRequest
  | .nil, _, _ => []
  | .cons head tail, cache, current =>
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

def Path.keys {source target : Type} : Path source target → List String
  | .self => []
  | @Path.stepField _ _ _ inst field rest => @Fields.key _ inst _ field :: rest.keys

mutual
/-- Key paths `component` writes to in its own value; nested values excluded. -/
def Component.writes {raw : Type} : Component raw → List (List String)
  | .field path .. => [path.keys]
  | .groupOf _ children => children.writes
  | .computed .. => []
  | .visibleWhen _ body => body.writes
  | .disabledWhen _ body => body.writes
  | .choiceOf path .. => [path.keys]
  | .list path .. => [path.keys]
  | .load _ body => body.writes.map (·.drop 1)
  | .keyedChoice (keyEq := _) (keyHash := _) (path := path) .. => [path.keys]

def Components.writes {raw : Type} : Components raw → List (List String)
  | .nil => []
  | .cons head tail => head.writes ++ tail.writes
end

/-- Whether every path in `writes` goes through `Scope.Field.value`. -/
def writesValue (writes : List (List String)) : Bool :=
  writes.all (·.head? == some (Scope.Field.value (context := Unit) (value := Unit)).key)

mutual
/-- Whether no `load` or `keyedChoice` body writes to its read-only context. -/
def Component.wellFormed {raw : Type} : Component raw → Bool
  | .field .. => true
  | .groupOf _ children => children.wellFormed
  | .computed .. => true
  | .visibleWhen _ body => body.wellFormed
  | .disabledWhen _ body => body.wellFormed
  | .choiceOf _ _ branches => branches.wellFormed
  | .list _ _ _ _ body => body.wellFormed
  | .load _ body => writesValue body.writes && body.wellFormed
  | .keyedChoice (keyEq := _) (keyHash := _) (body := body) .. =>
    writesValue body.writes && body.wellFormed

def Components.wellFormed {raw : Type} : Components raw → Bool
  | .nil => true
  | .cons head tail => head.wellFormed && tail.wellFormed

def Branch.wellFormed {sum : Type} : Branch sum → Bool
  | .mk _ _ _ _ _ body => body.wellFormed

def Branches.wellFormed {sum : Type} : Branches sum → Bool
  | .nil => true
  | .cons head tail => head.wellFormed && tail.wellFormed
end

end Forms.Model
