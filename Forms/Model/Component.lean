module

public import Forms.Model.Computation
public import Forms.Model.Remote

@[expose] public section
namespace Forms.Model

inductive Editor : Type → Type where
  | text : Editor String
  | natural : Editor Nat
  | checkbox : Editor Bool

mutual
inductive Component : Type → Type 1 where
  | field
      {raw value : Type}
      (path : Path raw value)
      (label : String)
      (editor : Editor value)
      : Component raw
  | groupOf
      {raw : Type}
      (label : String)
      (children : Components raw)
      : Component raw
  | computed
      {raw : Type}
      (label : String)
      (value : Computation raw String)
      : Component raw
  | visibleWhen
      {raw : Type}
      (condition : Computation raw Bool)
      (body : Component raw)
      : Component raw
  | disabledWhen
      {raw : Type}
      (condition : Computation raw Bool)
      (body : Component raw)
      : Component raw
  | choiceOf
      {raw sum : Type}
      (path : Path raw sum)
      (label : String)
      (branches : Branches sum)
      : Component raw
  /-- Edits each item of the list at `path` with `body`; added items start from `initial`. -/
  | list
      {raw item : Type}
      (path : Path raw (List item))
      (label itemLabel : String)
      (initial : item)
      (body : Component item)
      : Component raw
  /-- A list editor with one row per item and one component per column. -/
  | table
      {raw item : Type}
      (path : Path raw (List item))
      (label itemLabel : String)
      (initial : item)
      (columns : Columns item)
      : Component raw
  /-- Loads `source`; `body` builds the subtree from its status. -/
  | load
      {raw data : Type}
      (source : Computation raw (Source data))
      (body : Status data → Component raw)
      : Component raw

inductive Columns : Type → Type 1 where
  | nil {item : Type} : Columns item
  | cons
      {item : Type}
      (header : String)
      (cell : Component item)
      (rest : Columns item)
      : Columns item

inductive Components : Type → Type 1 where
  | nil {raw : Type} : Components raw
  | cons
      {raw : Type}
      (head : Component raw)
      (tail : Components raw)
      : Components raw

/-- One constructor of a `choice`; `body` edits its payload, starting from `initial` when chosen. -/
inductive Branch : Type → Type 1 where
  | mk
      {sum payload : Type}
      (key label : String)
      (inject : payload → sum)
      (project : sum → Option payload)
      (initial : payload)
      (body : Component payload)
      : Branch sum

inductive Branches : Type → Type 1 where
  | nil {sum : Type} : Branches sum
  | cons
      {sum : Type}
      (head : Branch sum)
      (tail : Branches sum)
      : Branches sum
end

def Components.ofList {raw : Type} : List (Component raw) → Components raw
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def Columns.ofList {item : Type} : List (String × Component item) → Columns item
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

def Columns.headers {item : Type} : Columns item → List String
  | .nil => []
  | .cons header _ rest => header :: rest.headers

def Columns.components {item : Type} : Columns item → Components item
  | .nil => .nil
  | .cons _ cell rest => .cons cell rest.components

def Component.group
  {raw : Type}
  (label : String)
  (children : List (Component raw))
  : Component raw :=
  .groupOf label (.ofList children)

def Branch.of
  {sum payload : Type}
  [Constructors sum]
  (constructor : Constructors.Constructor sum payload)
  (label : String)
  (initial : payload)
  (body : Component payload)
  : Branch sum :=
  .mk (Constructors.key constructor) label (Constructors.inject constructor)
    (Constructors.project constructor) initial body

def Branch.key {sum : Type} : Branch sum → String
  | .mk key .. => key

def Branch.label {sum : Type} : Branch sum → String
  | .mk _ label .. => label

/-- Whether `value` was built by this branch's constructor. -/
def Branch.matches {sum : Type} : Branch sum → sum → Bool
  | .mk _ _ _ project .., value => (project value).isSome

/-- The value a newly chosen branch starts from. -/
def Branch.start {sum : Type} : Branch sum → sum
  | .mk _ _ inject _ initial _ => inject initial

def Branches.ofList {sum : Type} : List (Branch sum) → Branches sum
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def Branches.toList {sum : Type} : Branches sum → List (Branch sum)
  | .nil => []
  | .cons head tail => head :: tail.toList

/-- Picks a constructor of the sum at `path`; the chosen branch edits its payload. -/
def Component.choice
  {raw sum : Type}
  (path : Path raw sum)
  (label : String)
  (branches : List (Branch sum))
  : Component raw :=
  .choiceOf path label (.ofList branches)

/-- Loads `source`; `body` builds the subtree from the data, with a note while loading or failed. -/
def Component.bind
  {raw data : Type}
  (source : Computation raw (Source data))
  (body : data → Component raw)
  : Component raw :=
  .load source fun
    | .ready data => body data
    | .loading => .computed "" (.const "Loading…")
    | .failed message => .computed "" (.const s!"Could not load: {message}")

/-- Loads `source`; `body` builds the subtree from the data, `fallback` stands in until then. -/
def Component.bindOr
  {raw data : Type}
  (source : Computation raw (Source data))
  (fallback : Component raw)
  (body : data → Component raw)
  : Component raw :=
  .load source fun
    | .ready data => body data
    | .loading => fallback
    | .failed _ => fallback

end Forms.Model
