module

public import Forms.Model.Component.Rename

@[expose] public section
namespace Forms.Model

/-- A component editing `α`, with private state, public output `β`, and `holes` places for
content that an enclosing layout fills. -/
structure Component (Γ : Context) (α : Type) (β : Type := Unit) (holes : Nat := 0) where
  LocalState : Type
  node : ComponentNode Γ α LocalState β holes

structure Presentation
    (slots : List Nat)
    (Γ : Context)
    (α : Type)
    (β : Type := Unit)
    (views : Nat := 1) where
  LocalState : Type
  node : PresentationNode slots Γ α LocalState β views

/-- Table cells: one view per header. -/
structure Columns (Γ : Context) (α : Type) (β : Type := Unit) where
  {count : Nat}
  headers : Vector String count
  cells : Presentation [] Γ α β count

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
  (label : Computation Γ α String)
  (active : Var Γ (Fin n))
  (tabs : Computation Γ α (Vector String n))
  : Component Γ α :=
  ⟨Unit, .tabBar label active tabs⟩

@[reducible] def Component.withAvailability
  {Γ : Context}
  {α β : Type}
  {holes : Nat}
  (availability : Computation Γ α Availability)
  (body : Component Γ α β holes)
  : Component Γ α β holes :=
  ⟨body.LocalState, .withAvailability availability body.node⟩

@[reducible] def Component.choiceOf
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  (label : Computation Γ α String)
  (branches : Branches Γ β)
  : Component Γ α :=
  ⟨branches.LocalState, .choiceOf path label branches.node⟩

/-- Shows `row` for each item at `path`, then the content of its hole.
Each row reads `Ref.row` and sets `Ref.rowRemoved` to remove itself. -/
@[reducible] def Component.listOf
  {Γ : Context}
  {α β γ : Type}
  (path : Path α (List β))
  (label : Computation Γ α String)
  (row : Component (Context.row β Γ) β γ)
  : Component Γ α (List γ) (holes := 1) :=
  ⟨List row.LocalState, .list path label row.node⟩

/-- Like `listOf`, with each row's views as cells under `headers` and its hole in the footer;
`selection` marks its row and follows removals. -/
@[reducible] def Component.tableOf
  {Γ : Context}
  {α β γ : Type}
  {columns : Nat}
  (path : Path α (List β))
  (label : Computation Γ α String)
  (headers : Computation Γ α (Vector String columns))
  (rowLabel : Computation (Context.row β Γ) β String)
  (row : Presentation [] (Context.row β Γ) β γ columns)
  (selection : Option (Var Γ RowSelection) := none)
  : Component Γ α (List γ) (holes := 1) :=
  ⟨List row.LocalState, .table path label headers rowLabel row.node selection⟩

@[reducible] def Component.focus
  {Γ : Context}
  {α β γ : Type}
  {holes : Nat}
  (target : Computation Γ α (PartialPath α β))
  (body : Component Γ β γ holes)
  : Component Γ α (Option γ) holes :=
  ⟨body.LocalState, .focus target body.node⟩

/-- Loaded subtree state persists while its resolved status is equal. -/
@[reducible] def Component.load
  {Γ : Context}
  {α β data : Type}
  {holes : Nat}
  [inst : DecidableEq data]
  (source : Computation Γ α (Source data))
  (body : Status data → Component Γ α β holes)
  : Component Γ α β holes :=
  ⟨LoadedState data (fun status => (body status).LocalState), .load source (fun status => (body status).node)⟩

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
  | .mk (project := project) .. => (project value).isSome

/-- The value a newly chosen branch starts from. -/
def Branch.start {Γ : Context} {α : Type} (branch : Branch Γ α) : α :=
  match branch.node with
  | .mk (inject := inject) (initial := initial) .. => inject initial

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
  (label : Computation Γ α String)
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

/-- Arranges the owned presentations into views with `arrangement` and returns `output`. -/
@[reducible] def Presentation.layouts
  {slots : List Nat}
  {Γ : Context}
  {α β : Type}
  {views : Nat}
  (output : Computation Γ α β)
  (arrangement : Computation Γ α (Vector (Layout slots) views))
  : Presentation slots Γ α β views :=
  ⟨Unit, .layout output arrangement⟩

/-- Places the owned presentations with `arrangement` and returns `output`. -/
@[reducible] def Presentation.layout
  {slots : List Nat}
  {Γ : Context}
  {α β : Type}
  (output : Computation Γ α β)
  (arrangement : Computation Γ α (Layout slots))
  : Presentation slots Γ α β :=
  .layouts output ((#v[·]) <$> arrangement)

/-- Places the owned presentations with `arrangement`. -/
@[reducible] def Presentation.arrange
  {slots : List Nat}
  {Γ : Context}
  {α : Type}
  (arrangement : Computation Γ α (Layout slots))
  : Presentation slots Γ α :=
  .layout (.const ()) arrangement

/-- Owns `component`: `body` reads its output as `Ref.here` and places its view as `Slot.here`. -/
@[reducible] def Presentation.own
  {slots : List Nat}
  {Γ : Context}
  {α β γ : Type}
  {holes views : Nat}
  (component : Component Γ α β holes)
  (body : Presentation (holes :: slots) (⟨.readOnly, β⟩ :: Γ) α γ views)
  : Presentation slots Γ α γ views :=
  ⟨ObservationState component.LocalState body.LocalState, .own component.node body.node⟩

@[reducible] def Presentation.bind
  {slots : List Nat}
  {Γ : Context}
  {α β γ : Type}
  {views : Nat}
  (initial : β)
  (body : Presentation slots (⟨.writable, β⟩ :: Γ) α γ views)
  : Presentation slots Γ α γ views :=
  ⟨Binding β body.LocalState, .bind initial body.node⟩

/-- Binds the active tab and owns its strip; `body` reads the tab as `.there .here` and places the
strip as `Slot.here`. -/
@[reducible] def Presentation.tabs
  {slots : List Nat}
  {n : Nat}
  {Γ : Context}
  {α β : Type}
  (label : Computation (⟨.writable, Fin (n + 1)⟩ :: Γ) α String)
  (labels : Computation (⟨.writable, Fin (n + 1)⟩ :: Γ) α (Vector String (n + 1)))
  (body : Presentation (0 :: slots) (⟨.readOnly, Unit⟩ :: ⟨.writable, Fin (n + 1)⟩ :: Γ) α β)
  : Presentation slots Γ α β :=
  .bind 0 (.own (.tabBar label .here labels) body)

/-- A component whose view is a layout of the components it owns. -/
@[reducible] def Component.present
  {Γ : Context}
  {α β : Type}
  (body : Presentation [] Γ α β)
  : Component Γ α β :=
  ⟨body.LocalState, .present body.node⟩

/-- Introduces writable local UI state for `body`. -/
@[reducible] def Component.bind
  {Γ : Context}
  {α β γ : Type}
  (initial : β)
  (body : Component (⟨.writable, β⟩ :: Γ) α γ)
  : Component Γ α γ :=
  .present <|
    .bind initial <|
      .own body <|
        .layout { inputs := inputs[.ui .here], run := id } (.const (.place .here))

@[reducible] def Component.rename
  {Γ Δ : Context}
  {α β : Type}
  {holes : Nat}
  (rename : Renaming Γ Δ)
  (component : Component Γ α β holes)
  : Component Δ α β holes :=
  ⟨component.LocalState, component.node.rename rename⟩

/-- Uses `component` under one more, innermost context entry, which it does not read. -/
@[reducible] def Component.weaken
  {Γ : Context}
  {entry : Entry}
  {α β : Type}
  {holes : Nat}
  (component : Component Γ α β holes)
  : Component (entry :: Γ) α β holes :=
  component.rename Renaming.shift

/-- Shows the presentations in `placed`, in order, in a group labeled by `label`. -/
@[reducible] def Layout.grouped
  {slots : List Nat}
  {Γ : Context}
  {α : Type}
  (label : Computation Γ α String)
  (placed : List (Slot slots 0))
  : Computation Γ α (Layout slots) :=
  (fun label => .group (some label) (placed.map Layout.place)) <$> label

/-- Owns `children` after the presentations in `placed`, then shows all of them in a group. -/
def Presentation.children
  {slots : List Nat}
  {Γ Δ : Context}
  {α : Type}
  (rename : Renaming Γ Δ)
  (label : Computation Δ α String)
  (placed : List (Slot slots 0))
  : List (Component Γ α) → Presentation slots Δ α
  | [] => .arrange (Layout.grouped label placed)
  | child :: rest =>
    .own (child.rename rename) <|
      Presentation.children (fun ref => .there (rename ref)) (label.rename Renaming.shift)
        (placed.map Slot.there ++ [.here]) rest

/-- Owns `cell` innermost in `cells` and places it after their views. -/
def PresentationNode.snoc
  {slots : List Nat}
  {Γ Δ : Context}
  {α state β : Type}
  {views : Nat}
  (cells : PresentationNode slots Δ α state β views)
  (rename : Renaming Γ Δ)
  (cell : Component Γ α)
  : Presentation slots Δ α β (views + 1) :=
  match cells with
  | .layout output arrangement =>
    .own (cell.rename rename) <|
      .layouts (output.rename Renaming.shift)
        ((fun layouts => (layouts.map (Layout.rename Slot.there)).push (.place .here)) <$>
          arrangement.rename Renaming.shift)
  | .own component body => .own ⟨_, component⟩ (body.snoc (fun ref => .there (rename ref)) cell)
  | .bind initial body => .bind initial (body.snoc (fun ref => .there (rename ref)) cell)

/-- Puts all views of `cells` in one group labeled `label`. -/
def PresentationNode.group
  {slots : List Nat}
  {Γ Δ : Context}
  {α state β : Type}
  {views : Nat}
  (cells : PresentationNode slots Δ α state β views)
  (rename : Renaming Γ Δ)
  (label : Computation Γ α String)
  : PresentationNode slots Δ α state β 1 :=
  match cells with
  | .layout output arrangement =>
    .layout output
      ((fun label layouts => #v[.group (some label) layouts.toList]) <$> label.rename rename <*>
        arrangement)
  | .own component body => .own component (body.group (fun ref => .there (rename ref)) label)
  | .bind initial body => .bind initial (body.group (fun ref => .there (rename ref)) label)

@[reducible] def Columns.nil {Γ : Context} {α : Type} : Columns Γ α :=
  ⟨#v[], .layouts (.const ()) (.const #v[])⟩

/-- Appends a column headed `header` that shows `cell`. -/
def Columns.snoc
  {Γ : Context}
  {α β : Type}
  (columns : Columns Γ α β)
  (header : String)
  (cell : Component Γ α)
  : Columns Γ α β :=
  ⟨columns.headers.push header, columns.cells.node.snoc (fun ref => ref) cell⟩

def Columns.ofList
  {Γ : Context}
  {α : Type}
  (columns : List (String × Component Γ α))
  : Columns Γ α :=
  columns.foldl (fun columns (header, cell) => columns.snoc header cell) .nil

declare_syntax_cat tableColumn
syntax term " => " term : tableColumn

/-- `columns["Name" => cell, "Amount" => otherCell]` pairs headers with cell components. -/
macro "columns[" columns:tableColumn,* "]" : term => do
  let mut result ← `(Columns.nil)
  for column in columns.getElems do
    match column with
    | `(tableColumn| $header:term => $cell:term) =>
      result ← `(Columns.snoc $result $header $cell)
    | _ => Lean.Macro.throwUnsupported
  return result

@[reducible] def Columns.rename
  {Γ Δ : Context}
  {α β : Type}
  (rename : Renaming Γ Δ)
  (columns : Columns Γ α β)
  : Columns Δ α β :=
  ⟨columns.headers, ⟨_, columns.cells.node.rename rename⟩⟩

/-- The cells of `columns` in a group labeled `label`, outputting the row output. -/
def Columns.group
  {Γ : Context}
  {α β : Type}
  (label : Computation Γ α String)
  (columns : Columns Γ α β)
  : Component Γ α β :=
  ⟨_, .present (columns.cells.node.group (fun ref => ref) label)⟩

/-- Renders `producer` followed by `body`.
The first entry in `body`'s context is the producer's current output, available read-only. -/
@[reducible] def Component.observe
  {Γ : Context}
  {α β γ : Type}
  (producer : Component Γ α β)
  (body : Component (⟨.readOnly, β⟩ :: Γ) α γ)
  : Component Γ α γ :=
  .present <|
    .own producer <|
      .own body <|
        .layout { inputs := inputs[.ui .here], run := id }
          (.const (.group none [.place (.there .here), .place .here]))

/-- Shows `first` above `second` and returns `second`'s output. -/
@[reducible] def Component.sequence
  {Γ : Context}
  {α β : Type}
  (first : Component Γ α Unit)
  (second : Component Γ α β)
  : Component Γ α β :=
  .observe first second.weaken

/-- Displays `view` and returns `output`. -/
@[reducible] def Component.withOutput
  {Γ : Context}
  {α β : Type}
  (view : Component Γ α)
  (output : Computation Γ α β)
  : Component Γ α β :=
  .sequence view (.output output)

/-- Keeps the component's UI and discards its public output. -/
@[reducible] def Component.void
  {Γ : Context}
  {α β : Type}
  (body : Component Γ α β)
  : Component Γ α :=
  .present (.own body (.arrange (.const (.place .here))))

/-- Fills the hole of `collection` with a button captioned `caption` that appends `initial` to the
list at `path`. -/
@[reducible] def Component.withAddButton
  {Γ : Context}
  {α β γ : Type}
  (path : Path α (List β))
  (caption : Computation Γ α String)
  (initial : β)
  (collection : Component Γ α γ (holes := 1))
  : Component Γ α γ :=
  .present <|
    .own collection <|
      .own (.button (caption.rename Renaming.shift) (.append path (.const initial))) <|
        .layout { inputs := inputs[.ui (Ref.there Ref.here)], run := id }
          (.const (.fill (.there .here) (.cons [.place .here] .nil)))

/-- Labels each row "`itemLabel` n", counting from 1. -/
@[reducible] def Computation.numbered
  {Γ : Context}
  {β : Type}
  (itemLabel : String)
  : Computation (Context.row β Γ) β String :=
  { inputs := inputs[.ui Ref.row], run := fun row => s!"{itemLabel} {row.index.val + 1}" }

/-- Lists the items at `path`, each in a group labeled `rowLabel` with a Remove button,
then an Add button captioned `addCaption` that appends `initial`. -/
@[reducible] def Component.list
  {Γ : Context}
  {α β γ : Type}
  (path : Path α (List β))
  (label : Computation Γ α String)
  (rowLabel : Computation (Context.row β Γ) β String)
  (addCaption : Computation Γ α String)
  (initial : β)
  (body : Component Γ β γ)
  : Component Γ α (List γ) :=
  let rowLabel := rowLabel.rename fun ref => .there (.there ref)
  .withAddButton path addCaption initial <| .listOf path label
    (.present <|
      .own (body.rename Renaming.row) <|
        .own (.button "Remove" (.set (.there Ref.rowRemoved) (.const true))) <|
          .layout { inputs := inputs[.ui (Ref.there Ref.here)], run := id }
            ((fun label => .group (some label) [.place (.there .here), .place .here]) <$> rowLabel))

/-- Tabulates the items at `path`, each row labeled `rowLabel`, with an Actions column holding
Remove (and Select, given `selection`) buttons, then an Add button captioned `addCaption` that
appends `initial`. -/
@[reducible] def Component.table
  {Γ : Context}
  {α β γ : Type}
  (path : Path α (List β))
  (label : Computation Γ α String)
  (rowLabel : Computation (Context.row β Γ) β String)
  (addCaption : Computation Γ α String)
  (initial : β)
  (columns : Columns Γ β γ)
  (selection : Option (Var Γ RowSelection) := none)
  : Component Γ α (List γ) :=
  let remove : Component (Context.row β Γ) β := .button "Remove" (.set Ref.rowRemoved (.const true))
  let actions : Component (Context.row β Γ) β := match selection with
    | none => remove
    | some selected =>
      .sequence
        (.button
          { inputs := inputs[.ui (Renaming.row selected), .ui Ref.row]
            run := fun current row => if current == .row row.index then "Selected" else "Select" }
          (.set (Renaming.row selected) { inputs := inputs[.ui Ref.row], run := fun row => .row row.index }))
        remove
  let columns := (columns.rename Renaming.row).snoc "Actions" actions
  .withAddButton path addCaption initial <|
    .tableOf path label (.const columns.headers) rowLabel columns.cells selection

/-- Shows `body` in a group labeled `label`, keeping its output. -/
@[reducible] def Component.labeled
  {Γ : Context}
  {α β : Type}
  (label : Computation Γ α String)
  (body : Component Γ α β)
  : Component Γ α β :=
  .present <|
    .own body <|
      .layout { inputs := inputs[.ui .here], run := id }
        (Layout.grouped (label.rename Renaming.shift) [.here])

/-- A group labeled `label` that owns `children` in order. -/
def Component.group
  {Γ : Context}
  {α : Type}
  (label : Computation Γ α String)
  (children : List (Component Γ α))
  : Component Γ α :=
  .present (Presentation.children (fun ref => ref) label [] children)

end Forms.Model
