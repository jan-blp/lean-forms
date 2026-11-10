module

public import Forms.Model.Component

@[expose] public section
namespace Forms.Model

inductive ListInvocation (item : Type) where
  | add
  | remove (index : Nat)
  | edit (index : Nat) (invocation : item)

inductive ValidListInvocation (length : Nat) (valid : Fin length → Type) where
  | add
  | remove (index : Fin length)
  | edit (index : Fin length) (invocation : valid index)

inductive BranchInvocation (payload : Type) where
  | select
  | edit (invocation : payload)

/-- A `BranchInvocation` checked against `current`, the active payload if this branch is active. -/
inductive ValidBranchInvocation
    {payload : Type}
    (current : Option payload)
    (valid : payload → Type)
    : Type where
  | select
  | edit (payload : payload) (active : current = some payload) (invocation : valid payload)

/-- The data a `load` checked `invocation` against. -/
structure ValidLoadInvocation {data : Type} (status : Status data) (valid : data → Type) where
  data : data
  ready : status = .ready data
  invocation : valid data

inductive KeyedInvocation (payload : Type) where
  | select (key : String)
  | edit (invocation : payload)

/-- A `KeyedInvocation` checked against `options` and the `selected` key. -/
inductive ValidKeyedInvocation
    {key payload : Type}
    (options : List (KeyedOption key))
    (selected : Option (key × payload))
    (valid : key → payload → Type)
    : Type where
  | select (option : KeyedOption key) (member : option ∈ options)
  | edit
      (picked : key)
      (payload : payload)
      (active : selected = some (picked, payload))
      (invocation : valid picked payload)

/-- Why an invocation does not apply to the current value. -/
inductive InvocationError where
  | hidden
  | disabled
  | inactiveBranch
  | indexOutOfBounds (index length : Nat)
  | notLoaded
  | unknownOption
  deriving DecidableEq, Repr

instance : ToString InvocationError where
  toString
    | .hidden => "This action is unavailable: the control is hidden."
    | .disabled => "This action is unavailable: the control is disabled."
    | .inactiveBranch => "This action is unavailable: the option is not selected."
    | .indexOutOfBounds index length =>
      s!"This action is unavailable: item {index + 1} of {length}."
    | .notLoaded => "This action is unavailable: the data is not loaded."
    | .unknownOption => "This action is unavailable: the option is no longer offered."

mutual
def Component.Invocation {raw : Type} : Component raw → Type
  | @Component.field _ value .. => value
  | .groupOf _ children => children.Invocation
  | .computed .. => Empty
  | .visibleWhen _ body => body.Invocation
  | .disabledWhen _ body => body.Invocation
  | .choiceOf _ _ branches => branches.Invocation
  | .list _ _ _ _ body => ListInvocation body.Invocation
  | .load _ body => body.Invocation
  | .keyedChoice (keyEq := _) (keyHash := _) (body := body) .. => KeyedInvocation body.Invocation

def Components.Invocation {raw : Type} : Components raw → Type
  | .nil => Empty
  | .cons head tail => head.Invocation ⊕ tail.Invocation

def Branch.Invocation {sum : Type} : Branch sum → Type
  | .mk _ _ _ _ _ body => BranchInvocation body.Invocation

def Branches.Invocation {sum : Type} : Branches sum → Type
  | .nil => Empty
  | .cons head tail => head.Invocation ⊕ tail.Invocation
end

mutual
/-- Invocations that apply to `current`: visible, enabled, in bounds, on the active branch and on
loaded data. -/
def Component.ValidInvocation {raw : Type} : Component raw → HttpRequest.Cache → raw → Type
  | @Component.field _ value .., _, _ => value
  | .groupOf _ children, cache, current => children.ValidInvocation cache current
  | .computed .., _, _ => Empty
  | .visibleWhen condition body, cache, current =>
    { _invocation : body.ValidInvocation cache current // condition.eval current = true }
  | .disabledWhen condition body, cache, current =>
    { _invocation : body.ValidInvocation cache current // condition.eval current = false }
  | .choiceOf path _ branches, cache, current => branches.ValidInvocation cache (path.get current)
  | .list path _ _ _ body, cache, current =>
    ValidListInvocation (path.get current).length fun index =>
      body.ValidInvocation cache ((path.get current).get index)
  | .load source body, cache, current =>
    ValidLoadInvocation ((source.eval current).resolve cache) fun data =>
      body.ValidInvocation cache ⟨data, current⟩
  | .keyedChoice (keyEq := _) (keyHash := _) (path := path) (options := options) (body := body) ..,
      cache, current =>
    ValidKeyedInvocation (options.eval current) (path.get current).selected fun picked payload =>
      body.ValidInvocation cache ⟨picked, payload⟩

def Components.ValidInvocation {raw : Type} : Components raw → HttpRequest.Cache → raw → Type
  | .nil, _, _ => Empty
  | .cons head tail, cache, current =>
    head.ValidInvocation cache current ⊕ tail.ValidInvocation cache current

def Branch.ValidInvocation {sum : Type} : Branch sum → HttpRequest.Cache → sum → Type
  | .mk _ _ _ project _ body, cache, current =>
    ValidBranchInvocation (project current) fun payload => body.ValidInvocation cache payload

def Branches.ValidInvocation {sum : Type} : Branches sum → HttpRequest.Cache → sum → Type
  | .nil, _, _ => Empty
  | .cons head tail, cache, current =>
    head.ValidInvocation cache current ⊕ tail.ValidInvocation cache current
end

def checkedIndex (index length : Nat) : Except InvocationError (Fin length) :=
  if h : index < length then
    .ok ⟨index, h⟩
  else
    .error (.indexOutOfBounds index length)

mutual
def Component.validate
  {raw : Type}
  (component : Component raw)
  (cache : HttpRequest.Cache)
  (current : raw)
  (invocation : component.Invocation)
  : Except InvocationError (component.ValidInvocation cache current) :=
  match component, invocation with
  | .field .., value => .ok value
  | .groupOf _ children, invocation => children.validate cache current invocation
  | .computed .., invocation => nomatch invocation
  | .visibleWhen condition body, invocation =>
    if h : condition.eval current = true then
      return ⟨← body.validate cache current invocation, h⟩
    else
      throw .hidden
  | .disabledWhen condition body, invocation =>
    if h : condition.eval current = false then
      return ⟨← body.validate cache current invocation, h⟩
    else
      throw .disabled
  | .choiceOf path _ branches, invocation => branches.validate cache (path.get current) invocation
  | .list path _ _ _ body, invocation =>
    let items := path.get current
    match (invocation : ListInvocation body.Invocation) with
    | .add => .ok ValidListInvocation.add
    | .remove index => return ValidListInvocation.remove (← checkedIndex index items.length)
    | .edit index invocation => do
      let index ← checkedIndex index items.length
      return ValidListInvocation.edit index (← body.validate cache (items.get index) invocation)
  | .load source body, invocation =>
    match ready : (source.eval current).resolve cache with
    | .ready data => return ⟨data, ready, ← body.validate cache ⟨data, current⟩ invocation⟩
    | .loading => throw .notLoaded
    | .failed _ => throw .notLoaded
  | .keyedChoice (keyEq := _) (keyHash := _) (path := path) (keyText := keyText)
      (options := options) (body := body) .., invocation =>
    match (invocation : KeyedInvocation body.Invocation) with
    | .select text =>
      match found : (options.eval current).find? (keyText ·.key == text) with
      | some option => .ok (ValidKeyedInvocation.select option (List.mem_of_find?_eq_some found))
      | none => throw .unknownOption
    | .edit invocation =>
      match active : (path.get current).selected with
      | none => throw .inactiveBranch
      | some (picked, payload) =>
        ValidKeyedInvocation.edit picked payload active <$>
          body.validate cache ⟨picked, payload⟩ invocation

def Components.validate
  {raw : Type}
  (children : Components raw)
  (cache : HttpRequest.Cache)
  (current : raw)
  (invocation : children.Invocation)
  : Except InvocationError (children.ValidInvocation cache current) :=
  match children, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.Invocation ⊕ tail.Invocation) with
    | .inl invocation => Sum.inl <$> head.validate cache current invocation
    | .inr invocation => Sum.inr <$> tail.validate cache current invocation

def Branch.validate
  {sum : Type}
  (branch : Branch sum)
  (cache : HttpRequest.Cache)
  (current : sum)
  (invocation : branch.Invocation)
  : Except InvocationError (branch.ValidInvocation cache current) :=
  match branch, invocation with
  | .mk _ _ _ project _ body, invocation =>
    match (invocation : BranchInvocation body.Invocation) with
    | .select => .ok ValidBranchInvocation.select
    | .edit invocation =>
      match active : project current with
      | some payload =>
        ValidBranchInvocation.edit payload active <$> body.validate cache payload invocation
      | none => throw .inactiveBranch

def Branches.validate
  {sum : Type}
  (branches : Branches sum)
  (cache : HttpRequest.Cache)
  (current : sum)
  (invocation : branches.Invocation)
  : Except InvocationError (branches.ValidInvocation cache current) :=
  match branches, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.Invocation ⊕ tail.Invocation) with
    | .inl invocation => Sum.inl <$> head.validate cache current invocation
    | .inr invocation => Sum.inr <$> tail.validate cache current invocation
end

mutual
def Component.applyValid
  {raw : Type}
  (component : Component raw)
  (cache : HttpRequest.Cache)
  (current : raw)
  (invocation : component.ValidInvocation cache current)
  : raw :=
  match component, invocation with
  | .field path .., value => path.set value current
  | .groupOf _ children, invocation => children.applyValid cache current invocation
  | .computed .., invocation => nomatch invocation
  | .visibleWhen _ body, invocation => body.applyValid cache current invocation.val
  | .disabledWhen _ body, invocation => body.applyValid cache current invocation.val
  | .choiceOf path _ branches, invocation =>
    path.set (branches.applyValid cache (path.get current) invocation) current
  | .list path _ _ initial body, invocation =>
    let items := path.get current
    let Valid index := body.ValidInvocation cache (items.get index)
    match (invocation : ValidListInvocation items.length Valid) with
    | .add => path.set (items ++ [initial]) current
    | .remove index => path.set (items.eraseIdx index) current
    | .edit index invocation =>
      path.set (items.set index (body.applyValid cache (items.get index) invocation)) current
  | .load source body, invocation =>
    let Valid data := body.ValidInvocation cache ⟨data, current⟩
    let invocation : ValidLoadInvocation ((source.eval current).resolve cache) Valid := invocation
    (body.applyValid cache ⟨invocation.data, current⟩ invocation.invocation).value
  | .keyedChoice (keyEq := _) (keyHash := _) (path := path) (options := options)
      (initial := initial) (body := body) .., invocation =>
    let selection := path.get current
    let Valid picked payload := body.ValidInvocation cache ⟨picked, payload⟩
    match (invocation : ValidKeyedInvocation (options.eval current) selection.selected Valid) with
    | .select option _ => path.set (selection.pick option.key initial) current
    | .edit picked payload _ invocation =>
      let edited := (body.applyValid cache ⟨picked, payload⟩ invocation).value
      path.set { selection with selected := some (picked, edited) } current

def Components.applyValid
  {raw : Type}
  (children : Components raw)
  (cache : HttpRequest.Cache)
  (current : raw)
  (invocation : children.ValidInvocation cache current)
  : raw :=
  match children, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.ValidInvocation cache current ⊕ tail.ValidInvocation cache current) with
    | .inl invocation => head.applyValid cache current invocation
    | .inr invocation => tail.applyValid cache current invocation

/-- Re-selecting the active branch keeps its payload. -/
def Branch.applyValid
  {sum : Type}
  (branch : Branch sum)
  (cache : HttpRequest.Cache)
  (current : sum)
  (invocation : branch.ValidInvocation cache current)
  : sum :=
  match branch, invocation with
  | .mk _ _ inject project initial body, invocation =>
    let Valid payload := body.ValidInvocation cache payload
    match (invocation : ValidBranchInvocation (project current) Valid) with
    | .select => if (project current).isSome then current else inject initial
    | .edit payload _ invocation => inject (body.applyValid cache payload invocation)

def Branches.applyValid
  {sum : Type}
  (branches : Branches sum)
  (cache : HttpRequest.Cache)
  (current : sum)
  (invocation : branches.ValidInvocation cache current)
  : sum :=
  match branches, invocation with
  | .nil, invocation => nomatch invocation
  | .cons head tail, invocation =>
    match (invocation : head.ValidInvocation cache current ⊕ tail.ValidInvocation cache current) with
    | .inl invocation => head.applyValid cache current invocation
    | .inr invocation => tail.applyValid cache current invocation
end

def Component.apply
  {raw : Type}
  (component : Component raw)
  (cache : HttpRequest.Cache)
  (current : raw)
  (invocation : component.Invocation)
  : Except InvocationError raw := do
  return component.applyValid cache current (← component.validate cache current invocation)

end Forms.Model
