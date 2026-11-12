module

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
  {raw item : Type}
  (items : Path raw (List item))
  : RowSelection → PartialPath raw item
  | .none => .empty
  | .row index => (PartialPath.ofPath items).trans (.index index .self)

mutual
inductive Component : Context → Type → Type 1 where
  | field {Γ : Context}
      {raw value : Type}
      (path : Path raw value)
      (label : String)
      (editor : Editor value)
      : Component Γ raw
  | groupOf {Γ : Context}
      {raw : Type}
      (label : String)
      (children : Components Γ raw)
      : Component Γ raw
  | computed {Γ : Context}
      {raw : Type}
      (label : String)
      (value : Computation Γ raw String)
      : Component Γ raw
  /-- Offers the same subtree as enabled, hidden, or disabled. -/
  | withAvailability {Γ : Context}
      {raw : Type}
      (availability : Computation Γ raw Availability)
      (body : Component Γ raw)
      : Component Γ raw
  | choiceOf {Γ : Context}
      {raw sum : Type}
      (path : Path raw sum)
      (label : String)
      (branches : Branches Γ sum)
      : Component Γ raw
  /-- Edits each item of the list at `path` with `body`; added items start from `initial`. -/
  | list {Γ : Context}
      {raw item : Type}
      (path : Path raw (List item))
      (label itemLabel : String)
      (initial : item)
      (body : Component Γ item)
      : Component Γ raw
  /-- A list editor with one row per item and one component per column. -/
  | table {Γ : Context}
      {raw item : Type}
      (path : Path raw (List item))
      (label itemLabel : String)
      (initial : item)
      (columns : Columns Γ item)
      (selection : Option (Var Γ RowSelection) := none)
      : Component Γ raw
  /-- Edits the value at the current partial path if present. -/
  | focus {Γ : Context}
      {raw value : Type}
      (target : Computation Γ raw (PartialPath raw value))
      (body : Component Γ value)
      : Component Γ raw
  /-- Introduces writable local UI state for `body`. -/
  | bind {Γ : Context}
      {raw α : Type}
      (initial : α)
      (body : Component (⟨.writable, α⟩ :: Γ) raw)
      : Component Γ raw
  /-- Loads `source`; `body` builds the subtree from its status.
  Local bindings persist while that status is equal and reset when it changes. -/
  | load {Γ : Context}
      {raw data : Type}
      [inst : DecidableEq data]
      (source : Computation Γ raw (Source data))
      (body : Status data → Component Γ raw)
      : Component Γ raw

inductive Columns : Context → Type → Type 1 where
  | nil {Γ : Context} {item : Type} : Columns Γ item
  | cons {Γ : Context}
      {item : Type}
      (header : String)
      (cell : Component Γ item)
      (rest : Columns Γ item)
      : Columns Γ item

inductive Components : Context → Type → Type 1 where
  | nil {Γ : Context} {raw : Type} : Components Γ raw
  | cons {Γ : Context}
      {raw : Type}
      (head : Component Γ raw)
      (tail : Components Γ raw)
      : Components Γ raw

/-- One constructor of a `choice`; `body` edits its payload, starting from `initial` when chosen. -/
inductive Branch : Context → Type → Type 1 where
  | mk {Γ : Context}
      {sum payload : Type}
      (key label : String)
      (inject : payload → sum)
      (project : sum → Option payload)
      (initial : payload)
      (body : Component Γ payload)
      : Branch Γ sum

inductive Branches : Context → Type → Type 1 where
  | nil {Γ : Context} {sum : Type} : Branches Γ sum
  | cons {Γ : Context}
      {sum : Type}
      (head : Branch Γ sum)
      (tail : Branches Γ sum)
      : Branches Γ sum
end

def Components.ofList {Γ : Context} {raw : Type} : List (Component Γ raw) → Components Γ raw
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def Columns.ofList {Γ : Context} {item : Type} : List (String × Component Γ item) → Columns Γ item
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

def Columns.headers {Γ : Context} {item : Type} : Columns Γ item → List String
  | .nil => []
  | .cons header _ rest => header :: rest.headers

def Columns.components {Γ : Context} {item : Type} : Columns Γ item → Components Γ item
  | .nil => .nil
  | .cons _ cell rest => .cons cell rest.components

def Component.group {Γ : Context}
  {raw : Type}
  (label : String)
  (children : List (Component Γ raw))
  : Component Γ raw :=
  .groupOf label (.ofList children)

def Branch.of {Γ : Context}
  {sum payload : Type}
  [Constructors sum]
  (constructor : Constructors.Constructor sum payload)
  (label : String)
  (initial : payload)
  (body : Component Γ payload)
  : Branch Γ sum :=
  .mk (Constructors.key constructor) label (Constructors.inject constructor)
    (Constructors.project constructor) initial body

def Branch.key {Γ : Context} {sum : Type} : Branch Γ sum → String
  | .mk key .. => key

def Branch.label {Γ : Context} {sum : Type} : Branch Γ sum → String
  | .mk _ label .. => label

/-- Whether `value` was built by this branch's constructor. -/
def Branch.matches {Γ : Context} {sum : Type} : Branch Γ sum → sum → Bool
  | .mk _ _ _ project .., value => (project value).isSome

/-- The value a newly chosen branch starts from. -/
def Branch.start {Γ : Context} {sum : Type} : Branch Γ sum → sum
  | .mk _ _ inject _ initial _ => inject initial

def Branches.ofList {Γ : Context} {sum : Type} : List (Branch Γ sum) → Branches Γ sum
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def Branches.toList {Γ : Context} {sum : Type} : Branches Γ sum → List (Branch Γ sum)
  | .nil => []
  | .cons head tail => head :: tail.toList

/-- Shows `body` only while `condition` holds. -/
def Component.visibleWhen
  {Γ : Context}
  {raw : Type}
  (condition : Computation Γ raw Bool)
  (body : Component Γ raw)
  : Component Γ raw :=
  .withAvailability ((fun visible => if visible then .enabled else .hidden) <$> condition) body

/-- Shows `body` read-only while `condition` holds. -/
def Component.disabledWhen
  {Γ : Context}
  {raw : Type}
  (condition : Computation Γ raw Bool)
  (body : Component Γ raw)
  : Component Γ raw :=
  .withAvailability ((fun disabled => if disabled then .disabled else .enabled) <$> condition) body

/-- Picks a constructor of the sum at `path`; the chosen branch edits its payload. -/
def Component.choice {Γ : Context}
  {raw sum : Type}
  (path : Path raw sum)
  (label : String)
  (branches : List (Branch Γ sum))
  : Component Γ raw :=
  .choiceOf path label (.ofList branches)

/-- Loads `source`; `body` builds the subtree from the data, with a note while loading or failed. -/
def Component.loadWith {Γ : Context}
  {raw data : Type}
  [DecidableEq data]
  (source : Computation Γ raw (Source data))
  (body : data → Component Γ raw)
  : Component Γ raw :=
  .load source fun
    | .ready data => body data
    | .loading => .computed "" (.const "Loading…")
    | .failed message => .computed "" (.const s!"Could not load: {message}")

/-- Loads `source`; `body` builds the subtree from the data, `fallback` stands in until then. -/
def Component.loadOr {Γ : Context}
  {raw data : Type}
  [DecidableEq data]
  (source : Computation Γ raw (Source data))
  (fallback : Component Γ raw)
  (body : data → Component Γ raw)
  : Component Γ raw :=
  .load source fun
    | .ready data => body data
    | .loading => fallback
    | .failed _ => fallback

end Forms.Model
