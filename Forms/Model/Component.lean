module

public import Forms.Model.Action
public import Forms.Model.PartialPath
public import Forms.Model.RowSelection
public import Forms.Model.Remote

@[expose] public section
namespace Forms.Model

inductive Editor : Type → Type where
  | text : Editor String
  | natural : Editor Nat
  | checkbox : Editor Bool

inductive Availability where
  | enabled
  | hidden
  | disabled
  deriving DecidableEq, Repr

/-- Turns a row selection into a concrete path to that list item. -/
def RowSelection.itemPath
  {α β : Type}
  (items : Path α (List β))
  : RowSelection → PartialPath α β
  | .none => .empty
  | .row index => (PartialPath.ofPath items).trans (.index index .self)

mutual
inductive Component : Context → Type → Type 1 where
  | field {Γ : Context}
      {α β : Type}
      (path : Path α β)
      (label : String)
      (editor : Editor β)
      : Component Γ α
  | groupOf {Γ : Context}
      {α : Type}
      (label : String)
      (children : Components Γ α)
      : Component Γ α
  | computed {Γ : Context}
      {α : Type}
      (label : String)
      (value : Computation Γ α String)
      : Component Γ α
  /-- Runs a UI state action when pressed. -/
  | button {Γ : Context}
      {α : Type}
      (label : String)
      (action : Action Γ α)
      : Component Γ α
  /-- Offers the same subtree as enabled, hidden, or disabled. -/
  | withAvailability {Γ : Context}
      {α : Type}
      (availability : Computation Γ α Availability)
      (body : Component Γ α)
      : Component Γ α
  | choiceOf {Γ : Context}
      {α β : Type}
      (path : Path α β)
      (label : String)
      (branches : Branches Γ β)
      : Component Γ α
  /-- Edits each item of the list at `path` with `body`; added items start from `initial`. -/
  | list {Γ : Context}
      {α β : Type}
      (path : Path α (List β))
      (label itemLabel : String)
      (initial : β)
      (body : Component Γ β)
      : Component Γ α
  /-- A list editor with one row per item and one component per column. -/
  | table {Γ : Context}
      {α β : Type}
      (path : Path α (List β))
      (label itemLabel : String)
      (initial : β)
      (columns : Columns Γ β)
      (selection : Option (Var Γ RowSelection) := none)
      : Component Γ α
  /-- Edits the value at the current partial path if present. -/
  | focus {Γ : Context}
      {α β : Type}
      (target : Computation Γ α (PartialPath α β))
      (body : Component Γ β)
      : Component Γ α
  /-- Introduces writable local UI state for `body`. -/
  | bind {Γ : Context}
      {α β : Type}
      (initial : β)
      (body : Component (⟨.writable, β⟩ :: Γ) α)
      : Component Γ α
  /-- Loads `source`; `body` builds the subtree from its status.
  Local bindings persist while that status is equal and reset when it changes. -/
  | load {Γ : Context}
      {α data : Type}
      [inst : DecidableEq data]
      (source : Computation Γ α (Source data))
      (body : Status data → Component Γ α)
      : Component Γ α

inductive Columns : Context → Type → Type 1 where
  | nil {Γ : Context} {α : Type} : Columns Γ α
  | cons {Γ : Context}
      {α : Type}
      (header : String)
      (cell : Component Γ α)
      (rest : Columns Γ α)
      : Columns Γ α

inductive Components : Context → Type → Type 1 where
  | nil {Γ : Context} {α : Type} : Components Γ α
  | cons {Γ : Context}
      {α : Type}
      (head : Component Γ α)
      (tail : Components Γ α)
      : Components Γ α

/-- One constructor of a `choice`; `body` edits its payload, starting from `initial` when chosen. -/
inductive Branch : Context → Type → Type 1 where
  | mk {Γ : Context}
      {α β : Type}
      (key label : String)
      (inject : β → α)
      (project : α → Option β)
      (initial : β)
      (body : Component Γ β)
      : Branch Γ α

inductive Branches : Context → Type → Type 1 where
  | nil {Γ : Context} {α : Type} : Branches Γ α
  | cons {Γ : Context}
      {α : Type}
      (head : Branch Γ α)
      (tail : Branches Γ α)
      : Branches Γ α
end

def Components.ofList {Γ : Context} {α : Type} : List (Component Γ α) → Components Γ α
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def Columns.ofList {Γ : Context} {α : Type} : List (String × Component Γ α) → Columns Γ α
  | [] => .nil
  | (header, cell) :: rest => .cons header cell (ofList rest)

declare_syntax_cat tableColumn
syntax term " => " term : tableColumn

/-- `columns["Name" => cell, "Amount" => otherCell]` pairs headers with cell components. -/
macro "columns[" columns:tableColumn,* "]" : term => do
  let mut result ← `(Columns.nil)
  for column in columns.getElems.reverse do
    match column with
    | `(tableColumn| $header:term => $cell:term) =>
      result ← `(Columns.cons $header $cell $result)
    | _ => Lean.Macro.throwUnsupported
  return result

def Columns.headers {Γ : Context} {α : Type} : Columns Γ α → List String
  | .nil => []
  | .cons header _ rest => header :: rest.headers

def Columns.components {Γ : Context} {α : Type} : Columns Γ α → Components Γ α
  | .nil => .nil
  | .cons _ cell rest => .cons cell rest.components

def Component.group
  {Γ : Context}
  {α : Type}
  (label : String)
  (children : List (Component Γ α))
  : Component Γ α :=
  .groupOf label (.ofList children)

def Branch.of
  {Γ : Context}
  {α β : Type}
  [Constructors α]
  (constructor : Constructors.Constructor α β)
  (label : String)
  (initial : β)
  (body : Component Γ β)
  : Branch Γ α :=
  .mk (Constructors.key constructor) label (Constructors.inject constructor)
    (Constructors.project constructor) initial body

def Branch.key {Γ : Context} {α : Type} : Branch Γ α → String
  | .mk key .. => key

def Branch.label {Γ : Context} {α : Type} : Branch Γ α → String
  | .mk _ label .. => label

/-- Whether `value` was built by this branch's constructor. -/
def Branch.matches {Γ : Context} {α : Type} : Branch Γ α → α → Bool
  | .mk _ _ _ project .., value => (project value).isSome

/-- The value a newly chosen branch starts from. -/
def Branch.start {Γ : Context} {α : Type} : Branch Γ α → α
  | .mk _ _ inject _ initial _ => inject initial

def Branches.ofList {Γ : Context} {α : Type} : List (Branch Γ α) → Branches Γ α
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def Branches.toList {Γ : Context} {α : Type} : Branches Γ α → List (Branch Γ α)
  | .nil => []
  | .cons head tail => head :: tail.toList

/-- Shows `body` only while `condition` holds. -/
def Component.visibleWhen
  {Γ : Context}
  {α : Type}
  (condition : Computation Γ α Bool)
  (body : Component Γ α)
  : Component Γ α :=
  .withAvailability ((fun visible => if visible then .enabled else .hidden) <$> condition) body

/-- Shows `body` read-only while `condition` holds. -/
def Component.disabledWhen
  {Γ : Context}
  {α : Type}
  (condition : Computation Γ α Bool)
  (body : Component Γ α)
  : Component Γ α :=
  .withAvailability ((fun disabled => if disabled then .disabled else .enabled) <$> condition) body

/-- Picks a constructor of the sum at `path`; the chosen branch edits its payload. -/
def Component.choice
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  (label : String)
  (branches : List (Branch Γ β))
  : Component Γ α :=
  .choiceOf path label (.ofList branches)

/-- Loads `source`; `body` builds the subtree from the data, with a note while loading or failed. -/
def Component.loadWith
  {Γ : Context}
  {α data : Type}
  [DecidableEq data]
  (source : Computation Γ α (Source data))
  (body : data → Component Γ α)
  : Component Γ α :=
  .load source fun
    | .ready data => body data
    | .loading => .computed "" (.const "Loading…")
    | .failed message => .computed "" (.const s!"Could not load: {message}")

/-- Loads `source`; `body` builds the subtree from the data, `fallback` stands in until then. -/
def Component.loadOr
  {Γ : Context}
  {α data : Type}
  [DecidableEq data]
  (source : Computation Γ α (Source data))
  (fallback : Component Γ α)
  (body : data → Component Γ α)
  : Component Γ α :=
  .load source fun
    | .ready data => body data
    | .loading => fallback
    | .failed _ => fallback

end Forms.Model
