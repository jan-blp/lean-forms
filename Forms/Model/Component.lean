module

public import Forms.Model.Component.Rename

@[expose] public section
namespace Forms.Model

/-- A component editing `α`, with private state and public output `β`. -/
structure Component (Γ : Context) (α : Type) (β : Type := Unit) where
  LocalState : Type
  node : ComponentNode Γ α LocalState β

structure Columns (Γ : Context) (α : Type) (β : Type := Unit) where
  headers : List String
  LocalState : Type
  node : ColumnsNode headers Γ α LocalState β

structure Presentation (slots : Nat) (Γ : Context) (α : Type) (β : Type := Unit) where
  LocalState : Type
  node : PresentationNode slots Γ α LocalState β

structure Branch (Γ : Context) (α : Type) where
  pack ::
  LocalState : Type
  node : BranchNode Γ α LocalState

structure Branches (Γ : Context) (α : Type) where
  LocalState : Type
  node : BranchesNode Γ α LocalState

/-- Turns a row selection into a concrete path to that list item. -/
def RowSelection.itemPath
  {α β : Type}
  (items : Path α (List β))
  : RowSelection → PartialPath α β
  | .none => .empty
  | .row index => (PartialPath.ofPath items).trans (.index index .self)

/-- Returns a computed output without adding any UI. -/
@[reducible] def Component.output
  {Γ : Context}
  {α β : Type}
  (value : Computation Γ α β)
  : Component Γ α β :=
  ⟨Unit, .output value⟩

@[reducible] def Component.sequence
  {Γ : Context}
  {α β : Type}
  (first : Component Γ α Unit)
  (second : Component Γ α β)
  : Component Γ α β :=
  ⟨Binding first.LocalState second.LocalState, .sequence first.node second.node⟩

/-- Displays `view` and returns `output`. -/
@[reducible] def Component.withOutput
  {Γ : Context}
  {α β : Type}
  (view : Component Γ α)
  (output : Computation Γ α β)
  : Component Γ α β :=
  .sequence view (.output output)

@[reducible] def Component.field
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  (label : Computation Γ α String)
  (editor : Editor β)
  : Component Γ α :=
  ⟨Unit, .field path label editor⟩

@[reducible] def Component.computed
  {Γ : Context}
  {α : Type}
  (label : String)
  (value : Computation Γ α String)
  : Component Γ α :=
  ⟨Unit, .computed label value⟩

@[reducible] def Component.button
  {Γ : Context}
  {α : Type}
  (caption : Computation Γ α String)
  (action : Action Γ α)
  : Component Γ α :=
  ⟨Unit, .button caption action⟩

@[reducible] def Component.tabBar
  {Γ : Context}
  {α : Type}
  {n : Nat}
  (label : String)
  (active : Var Γ (Fin n))
  (tabs : Computation Γ α (Vector String n))
  : Component Γ α :=
  ⟨Unit, .tabBar label active tabs⟩

@[reducible] def Component.withAvailability
  {Γ : Context}
  {α β : Type}
  (availability : Computation Γ α Availability)
  (body : Component Γ α β)
  : Component Γ α β :=
  ⟨body.LocalState, .withAvailability availability body.node⟩

@[reducible] def Component.choiceOf
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  (label : String)
  (branches : Branches Γ β)
  : Component Γ α :=
  ⟨branches.LocalState, .choiceOf path label branches.node⟩

@[reducible] def Component.list
  {Γ : Context}
  {α β γ : Type}
  (path : Path α (List β))
  (label itemLabel : String)
  (initial : β)
  (body : Component Γ β γ)
  : Component Γ α (List γ) :=
  ⟨List body.LocalState, .list path label itemLabel initial body.node⟩

@[reducible] def Component.table
  {Γ : Context}
  {α β γ : Type}
  (path : Path α (List β))
  (label itemLabel : String)
  (initial : β)
  (columns : Columns Γ β γ)
  (selection : Option (Var Γ RowSelection) := none)
  : Component Γ α (List γ) :=
  ⟨List columns.LocalState, .table path label itemLabel initial columns.node selection⟩

@[reducible] def Component.focus
  {Γ : Context}
  {α β γ : Type}
  (target : Computation Γ α (PartialPath α β))
  (body : Component Γ β γ)
  : Component Γ α (Option γ) :=
  ⟨body.LocalState, .focus target body.node⟩

/-- Introduces writable local UI state for `body`. -/
@[reducible] def Component.bind
  {Γ : Context}
  {α β γ : Type}
  (initial : β)
  (body : Component (⟨.writable, β⟩ :: Γ) α γ)
  : Component Γ α γ :=
  ⟨Binding β body.LocalState, .bind initial body.node⟩

/-- Loaded subtree state persists while its resolved status is equal. -/
@[reducible] def Component.load
  {Γ : Context}
  {α β data : Type}
  [inst : DecidableEq data]
  (source : Computation Γ α (Source data))
  (body : Status data → Component Γ α β)
  : Component Γ α β :=
  ⟨LoadedState data (fun status => (body status).LocalState), .load source (fun status => (body status).node)⟩

/-- Renders `producer` followed by `body`.
The first entry in `body`'s context is the producer's current output, available read-only. -/
@[reducible] def Component.observe
  {Γ : Context}
  {α β γ : Type}
  (producer : Component Γ α β)
  (body : Component (⟨.readOnly, β⟩ :: Γ) α γ)
  : Component Γ α γ :=
  ⟨ObservationState producer.LocalState body.LocalState, .observe producer.node body.node⟩

@[reducible] def Columns.nil {Γ : Context} {α : Type} : Columns Γ α Unit :=
  ⟨[], Unit, .output (.const ())⟩

@[reducible] def Columns.output
  {Γ : Context}
  {α β : Type}
  (value : Computation Γ α β)
  : Columns Γ α β :=
  ⟨[], Unit, .output value⟩

@[reducible] def Columns.cons
  {Γ : Context}
  {α β : Type}
  (header : String)
  (cell : Component Γ α Unit)
  (rest : Columns Γ α β)
  : Columns Γ α β :=
  ⟨header :: rest.headers, Binding cell.LocalState rest.LocalState,
    .cons header cell.node rest.node⟩

/-- Makes a cell's output available read-only to the remaining columns and row output. -/
@[reducible] def Columns.observe
  {Γ : Context}
  {α β γ : Type}
  (header : String)
  (cell : Component Γ α β)
  (body : Columns (⟨.readOnly, β⟩ :: Γ) α γ)
  : Columns Γ α γ :=
  ⟨header :: body.headers, ObservationState cell.LocalState body.LocalState,
    .observe header cell.node body.node⟩

@[reducible] def Columns.bind
  {Γ : Context}
  {α β γ : Type}
  (initial : β)
  (body : Columns (⟨.writable, β⟩ :: Γ) α γ)
  : Columns Γ α γ :=
  ⟨body.headers, Binding β body.LocalState, .bind initial body.node⟩

/-- Focuses every cell on the same optional value, retaining the column headers. -/
@[reducible] def Columns.focus
  {Γ : Context}
  {α β γ : Type}
  (target : Computation Γ α (PartialPath α β))
  (body : Columns Γ β γ)
  : Columns Γ α (Option γ) :=
  ⟨body.headers, body.LocalState, .focus target body.node⟩

@[reducible] def Branches.nil {Γ : Context} {α : Type} : Branches Γ α :=
  ⟨Unit, .nil⟩

@[reducible] def Branches.cons
  {Γ : Context}
  {α : Type}
  (head : Branch Γ α)
  (tail : Branches Γ α)
  : Branches Γ α :=
  ⟨Binding head.LocalState tail.LocalState, .cons head.node tail.node⟩

@[reducible] def Branch.mk
  {Γ : Context}
  {α β : Type}
  (key label : String)
  (inject : β → α)
  (project : α → Option β)
  (initial : β)
  (body : Component Γ β)
  : Branch Γ α :=
  ⟨body.LocalState, .mk key label inject project initial body.node⟩

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

def Branch.key {Γ : Context} {α : Type} (branch : Branch Γ α) : String :=
  match branch.node with
  | .mk key .. => key

def Branch.label {Γ : Context} {α : Type} (branch : Branch Γ α) : String :=
  match branch.node with
  | .mk _ label .. => label

/-- Whether `value` was built by this branch's constructor. -/
def Branch.matches {Γ : Context} {α : Type} (branch : Branch Γ α) (value : α) : Bool :=
  match branch.node with
  | .mk _ _ _ project .. => (project value).isSome

/-- The value a newly chosen branch starts from. -/
def Branch.start {Γ : Context} {α : Type} (branch : Branch Γ α) : α :=
  match branch.node with
  | .mk _ _ inject _ initial _ => inject initial

def Branches.ofList {Γ : Context} {α : Type} : List (Branch Γ α) → Branches Γ α
  | [] => .nil
  | head :: tail => .cons head (ofList tail)

def BranchesNode.toList {Γ : Context} {α state : Type} : BranchesNode Γ α state → List (Branch Γ α)
  | .nil => []
  | .cons head tail => ⟨_, head⟩ :: tail.toList

def Branches.toList {Γ : Context} {α : Type} (branches : Branches Γ α) : List (Branch Γ α) :=
  branches.node.toList

/-- Shows `body` only while `condition` holds. -/
def Component.visibleWhen
  {Γ : Context}
  {α β : Type}
  (condition : Computation Γ α Bool)
  (body : Component Γ α β)
  : Component Γ α β :=
  .withAvailability ((fun visible => if visible then .enabled else .hidden) <$> condition) body

/-- Shows `body` read-only while `condition` holds. -/
def Component.disabledWhen
  {Γ : Context}
  {α β : Type}
  (condition : Computation Γ α Bool)
  (body : Component Γ α β)
  : Component Γ α β :=
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
  [inst : DecidableEq data]
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
  [inst : DecidableEq data]
  (source : Computation Γ α (Source data))
  (fallback : Component Γ α)
  (body : data → Component Γ α)
  : Component Γ α :=
  .load source fun
    | .ready data => body data
    | .loading => fallback
    | .failed _ => fallback

/-- Keeps the component's UI and discards its public output. -/
@[reducible] def Component.void
  {Γ : Context}
  {α β : Type}
  (body : Component Γ α β)
  : Component Γ α :=
  ⟨body.LocalState, .void body.node⟩

/-- Adds a group label without changing the body's output. -/
@[reducible] def Component.labeled
  {Γ : Context}
  {α β : Type}
  (label : String)
  (body : Component Γ α β)
  : Component Γ α β :=
  ⟨body.LocalState, .labeled label body.node⟩

/-- Places the owned presentations with `arrangement` and returns `output`. -/
@[reducible] def Presentation.layout
  {slots : Nat}
  {Γ : Context}
  {α β : Type}
  (output : Computation Γ α β)
  (arrangement : Computation Γ α (Layout slots))
  : Presentation slots Γ α β :=
  ⟨Unit, .layout output arrangement⟩

/-- Places the owned presentations with `arrangement`. -/
@[reducible] def Presentation.arrange
  {slots : Nat}
  {Γ : Context}
  {α : Type}
  (arrangement : Computation Γ α (Layout slots))
  : Presentation slots Γ α :=
  .layout (.const ()) arrangement

/-- Owns `component`: `body` reads its output as `Ref.here` and places its view as `Slot.here`. -/
@[reducible] def Presentation.own
  {slots : Nat}
  {Γ : Context}
  {α β γ : Type}
  (component : Component Γ α β)
  (body : Presentation (slots + 1) (⟨.readOnly, β⟩ :: Γ) α γ)
  : Presentation slots Γ α γ :=
  ⟨ObservationState component.LocalState body.LocalState, .own component.node body.node⟩

@[reducible] def Presentation.bind
  {slots : Nat}
  {Γ : Context}
  {α β γ : Type}
  (initial : β)
  (body : Presentation slots (⟨.writable, β⟩ :: Γ) α γ)
  : Presentation slots Γ α γ :=
  ⟨Binding β body.LocalState, .bind initial body.node⟩

/-- Binds the active tab and owns its strip; `body` reads the tab as `.there .here` and places the
strip as `Slot.here`. -/
@[reducible] def Presentation.tabs
  {slots n : Nat}
  {Γ : Context}
  {α β : Type}
  (label : String)
  (labels : Computation (⟨.writable, Fin (n + 1)⟩ :: Γ) α (Vector String (n + 1)))
  (body : Presentation (slots + 1) (⟨.readOnly, Unit⟩ :: ⟨.writable, Fin (n + 1)⟩ :: Γ) α β)
  : Presentation slots Γ α β :=
  .bind 0 (.own (.tabBar label .here labels) body)

/-- A component whose view is a layout of the components it owns. -/
@[reducible] def Component.present
  {Γ : Context}
  {α β : Type}
  (body : Presentation 0 Γ α β)
  : Component Γ α β :=
  ⟨body.LocalState, .present body.node⟩

@[reducible] def Component.rename
  {Γ Δ : Context}
  {α β : Type}
  (rename : Renaming Γ Δ)
  (component : Component Γ α β)
  : Component Δ α β :=
  ⟨component.LocalState, component.node.rename rename⟩

/-- Uses `component` under one more, innermost context entry, which it does not read. -/
@[reducible] def Component.weaken
  {Γ : Context}
  {entry : Entry}
  {α β : Type}
  (component : Component Γ α β)
  : Component (entry :: Γ) α β :=
  component.rename Renaming.shift

/-- Shows the presentations in `placed`, in order, in a group labeled by `label`. -/
@[reducible] def Layout.grouped
  {slots : Nat}
  {Γ : Context}
  {α : Type}
  (label : Computation Γ α String)
  (placed : List (Slot slots))
  : Computation Γ α (Layout slots) :=
  (fun label => .group (some label) (placed.map Layout.place)) <$> label

/-- Owns `children` after the presentations in `placed`, then shows all of them in a group. -/
def Presentation.children
  {slots : Nat}
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  (label : Computation Δ α String)
  (placed : List (Slot slots))
  : List (Component Γ α) → Presentation slots Δ α
  | [] => .arrange (Layout.grouped label placed)
  | child :: rest =>
    .own (child.rename rename) <|
      Presentation.children (fun ref => .there (rename ref)) (label.rename Renaming.shift)
        (placed.map Slot.there ++ [.here]) rest

/-- Owns each cell after the presentations in `placed`, then shows all of them in a group;
the output is the row output. -/
def ColumnsNode.presentation
  {headers : List String}
  {slots : Nat}
  {Γ Δ : Context}
  {α state β : Type}
  (columns : ColumnsNode headers Γ α state β)
  (rename : Renaming Γ Δ)
  (label : Computation Δ α String)
  (placed : List (Slot slots))
  : Presentation slots Δ α β :=
  match columns with
  | .output value => .layout (value.rename rename) (Layout.grouped label placed)
  | .cons _ cell rest =>
    .own ⟨_, cell.rename rename⟩ <|
      rest.presentation (fun ref => .there (rename ref)) (label.rename Renaming.shift)
        (placed.map Slot.there ++ [.here])
  | .observe _ cell rest =>
    .own ⟨_, cell.rename rename⟩ <|
      rest.presentation rename.lift (label.rename Renaming.shift) (placed.map Slot.there ++ [.here])
  | .bind initial body =>
    .bind initial (body.presentation rename.lift (label.rename Renaming.shift) placed)
  | .focus target body =>
    let body := Component.present (body.presentation (fun ref => ref) (.const "") [])
    let focused : Component _ _ _ := ⟨_, .focus target body.node⟩
    .own (focused.rename rename) <|
      .layout { inputs := inputs[.ui .here], run := id }
        (Layout.grouped (label.rename Renaming.shift) (placed.map Slot.there ++ [.here]))

/-- A group labeled `label` that owns `children` in order. -/
def Component.group
  {Γ : Context}
  {α : Type}
  (label : Computation Γ α String)
  (children : List (Component Γ α))
  : Component Γ α :=
  .present (Presentation.children (fun ref => ref) label [] children)

/-- The cells of `columns` as a group labeled `label`, outputting the row output. -/
def Columns.group
  {Γ : Context}
  {α β : Type}
  (label : Computation Γ α String)
  (columns : Columns Γ α β)
  : Component Γ α β :=
  .present (columns.node.presentation (fun ref => ref) label [])

end Forms.Model
