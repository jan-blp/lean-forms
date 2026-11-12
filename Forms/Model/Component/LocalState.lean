module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model

/-- A single-entry cache of subtree state, keyed by the resolved load status. -/
structure LoadedState (data : Type) (state : Status data → Type) where
  status : Status data
  body : state status

/-- Looks up `status` in the single-entry cache, returning `initial` on a miss. -/
def LoadedState.at
  {data : Type}
  [DecidableEq data]
  {state : Status data → Type}
  (stored : LoadedState data state)
  (status : Status data)
  (initial : state status)
  : state status :=
  if same : stored.status = status then same ▸ stored.body else initial

mutual
/-- Local state follows the component structure, so every binding keeps its own typed value. -/
@[reducible] def Component.LocalState {Γ : List Type} {raw : Type} : Component Γ raw → Type
  | .field .. => Unit
  | .computed .. => Unit
  | .groupOf _ children => children.LocalState
  | .withAvailability _ body => body.LocalState
  | .choiceOf (branches := branches) .. => branches.LocalState
  | .list (body := body) .. => List body.LocalState
  | .table (columns := columns) .. => List columns.LocalState
  | .focus _ body => body.LocalState
  | .bind (α := α) (body := body) .. => Binding α body.LocalState
  | .load (data := data) (inst := _inst) (body := body) .. => LoadedState data (fun status => (body status).LocalState)

@[reducible] def Components.LocalState {Γ : List Type} {raw : Type} : Components Γ raw → Type
  | .nil => Unit
  | .cons head tail => Binding head.LocalState tail.LocalState

@[reducible] def Columns.LocalState {Γ : List Type} {raw : Type} : Columns Γ raw → Type
  | .nil => Unit
  | .cons _ head tail => Binding head.LocalState tail.LocalState

@[reducible] def Branch.LocalState {Γ : List Type} {raw : Type} : Branch Γ raw → Type
  | .mk (body := body) .. => body.LocalState

@[reducible] def Branches.LocalState {Γ : List Type} {raw : Type} : Branches Γ raw → Type
  | .nil => Unit
  | .cons head tail => Binding head.LocalState tail.LocalState
end

mutual
def Component.initialState {Γ : List Type} {raw : Type} (component : Component Γ raw)
    : component.LocalState :=
  match component with
  | .field .. => ()
  | .computed .. => ()
  | .groupOf _ children => children.initialState
  | .withAvailability _ body => body.initialState
  | .choiceOf (branches := branches) .. => branches.initialState
  | .list .. => []
  | .table .. => []
  | .focus _ body => body.initialState
  | .bind initial body => ⟨initial, body.initialState⟩
  | .load (inst := _inst) (body := body) .. => ⟨.loading, (body .loading).initialState⟩

def Components.initialState {Γ : List Type} {raw : Type} (children : Components Γ raw)
    : children.LocalState :=
  match children with
  | .nil => ()
  | .cons head tail => ⟨head.initialState, tail.initialState⟩

def Columns.initialState {Γ : List Type} {raw : Type} (columns : Columns Γ raw)
    : columns.LocalState :=
  match columns with
  | .nil => ()
  | .cons _ head tail => ⟨head.initialState, tail.initialState⟩

def Branch.initialState {Γ : List Type} {raw : Type} (branch : Branch Γ raw)
    : branch.LocalState :=
  match branch with
  | .mk (body := body) .. => body.initialState

def Branches.initialState {Γ : List Type} {raw : Type} (branches : Branches Γ raw)
    : branches.LocalState :=
  match branches with
  | .nil => ()
  | .cons head tail => ⟨head.initialState, tail.initialState⟩
end

mutual
/-- Initializes new rows and resets loaded subtree state when its status changes. -/
def Component.normalize {Γ : List Type} {raw : Type} (component : Component Γ raw)
    (cache : HttpRequest.Cache) (current : raw) (env : Env Γ) (locals : component.LocalState)
    : component.LocalState :=
  match component with
  | .field .. => locals
  | .computed .. => locals
  | .groupOf _ children => children.normalize cache current env locals
  | .withAvailability _ body => body.normalize cache current env locals
  | .choiceOf path _ branches => branches.normalize cache (path.get current) env locals
  | .list (path := path) (body := body) .. =>
    (path.get current).mapIdx fun index value =>
      body.normalize cache value env (locals[index]?.getD body.initialState)
  | .table (path := path) (columns := columns) .. =>
    (path.get current).mapIdx fun index value =>
      columns.normalize cache value env (locals[index]?.getD columns.initialState)
  | .focus target body =>
    match (target.eval current env).get? current with
    | none => locals
    | some value => body.normalize cache value env locals
  | .bind _ body => ⟨locals.value, body.normalize cache current (Env.cons locals.value env) locals.tail⟩
  | .load (inst := _inst) (source := source) (body := body) .. =>
    let status := (source.eval current env).resolve cache
    ⟨status, (body status).normalize cache current env (locals.at status (body status).initialState)⟩

def Components.normalize {Γ : List Type} {raw : Type} (children : Components Γ raw)
    (cache : HttpRequest.Cache) (current : raw) (env : Env Γ) (locals : children.LocalState)
    : children.LocalState :=
  match children with
  | .nil => locals
  | .cons head tail => ⟨head.normalize cache current env locals.value, tail.normalize cache current env locals.tail⟩

def Columns.normalize {Γ : List Type} {raw : Type} (columns : Columns Γ raw)
    (cache : HttpRequest.Cache) (current : raw) (env : Env Γ) (locals : columns.LocalState)
    : columns.LocalState :=
  match columns with
  | .nil => locals
  | .cons _ head tail => ⟨head.normalize cache current env locals.value, tail.normalize cache current env locals.tail⟩

def Branch.normalize {Γ : List Type} {raw : Type} (branch : Branch Γ raw)
    (cache : HttpRequest.Cache) (current : raw) (env : Env Γ) (locals : branch.LocalState)
    : branch.LocalState :=
  match branch with
  | .mk _ _ _ project _ body =>
    match project current with
    | none => locals
    | some value => body.normalize cache value env locals

def Branches.normalize {Γ : List Type} {raw : Type} (branches : Branches Γ raw)
    (cache : HttpRequest.Cache) (current : raw) (env : Env Γ) (locals : branches.LocalState)
    : branches.LocalState :=
  match branches with
  | .nil => locals
  | .cons head tail => ⟨head.normalize cache current env locals.value, tail.normalize cache current env locals.tail⟩
end

end Forms.Model
