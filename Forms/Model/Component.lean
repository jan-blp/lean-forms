module

public import Forms.Model.RowSelection
public import Forms.Model.Report
public import Forms.Model.Component.Rename

@[expose] public section
namespace Forms.Model

/-- A component editing `α`, with private state, public output `β`, and `holes` places for
content that an enclosing layout fills. -/
structure Component (Γ : Context) (α : Type) (β : Type := Unit) (holes : Nat := 0) where
  LocalState : Type
  node : ComponentNode Γ α LocalState β holes

structure Presentation
    (Δ : ViewContext)
    (Γ : Context)
    (α : Type)
    (β : Type := Unit)
    (views : Nat := 1) where
  LocalState : Type
  node : PresentationNode Δ Γ α LocalState β views

/-- Table cells: one view per header. -/
structure Columns (Γ : Context) (α : Type) (β : Type := Unit) where
  {count : Nat}
  headers : Vector String count
  cells : Presentation [] Γ α β count

structure Branch (Γ : Context) (α : Type) [Constructors α] where
  {Payload : Type}
  constructor : Constructors.Constructor α Payload
  label : String
  initial : Payload
  body : Component Γ Payload

abbrev Component.issues
  {Γ : Context}
  {α : Type}
  : Component Γ α (List Issue) :=
  { LocalState := Unit, node := .issues }

abbrev Component.reports
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  : Component Γ α (List ReportMessage) :=
  { LocalState := Unit, node := .reports path }

abbrev Component.statusMarker
  {Γ : Context}
  {α : Type}
  (reports : Computation Γ α (List ReportMessage))
  : Component Γ α :=
  { LocalState := Unit, node := .statusMarker reports }

def RowSelection.itemPath
  {α β : Type}
  (items : Path α (Collection β))
  : RowSelection → Option (PartialPath α β)
  | .none => Option.none
  | .row id => some ((PartialPath.ofPath items).trans (.item id .self))

abbrev Component.output
  {Γ : Context}
  {α β : Type}
  (value : Computation Γ α β)
  : Component Γ α β :=
  { LocalState := Unit, node := .output value }

abbrev Component.field
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  (label : Computation Γ α String)
  (editor : Editor β)
  : Component Γ α :=
  { LocalState := Unit, node := .field (.path path) label editor .none }

abbrev Component.stateField
  {Γ : Context}
  {α β : Type}
  (var : Var Γ β)
  (label : Computation Γ α String)
  (editor : Editor β)
  : Component Γ α :=
  { LocalState := Unit, node := .field (.var var) label editor .none }

abbrev Component.fieldWithEvidence
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  (evidence : EvidenceSlot α β)
  (label : Computation Γ α String)
  (editor : Editor β)
  : Component Γ α :=
  { LocalState := Unit, node := .field (.path path) label editor (.recordedAt evidence) }

abbrev Component.computed
  {Γ : Context}
  {α : Type}
  (label : Computation Γ α String)
  (value : Computation Γ α String)
  : Component Γ α :=
  { LocalState := Unit, node := .computed label value }

abbrev Component.button
  {Γ : Context}
  {α : Type}
  (caption : Computation Γ α String)
  (action : Action Γ α)
  : Component Γ α :=
  { LocalState := Option PendingCall, node := .button caption action }

abbrev Component.tabBar
  {Γ : Context}
  {α : Type}
  {n : Nat}
  (label : Computation Γ α String)
  (active : Var Γ (Fin n))
  (tabs : Computation Γ α (Vector String n))
  : Component Γ α :=
  { LocalState := Unit, node := .tabBar label active tabs }

abbrev Component.withAvailability
  {Γ : Context}
  {α β : Type}
  {holes : Nat}
  (availability : Computation Γ α Availability)
  (body : Component Γ α β holes)
  : Component Γ α β holes :=
  { LocalState := body.LocalState, node := .withAvailability availability body.node }

abbrev Component.onChange
  {Γ : Context}
  {α β : Type}
  {holes : Nat}
  (react : (old new : α) → Action Γ α)
  (body : Component Γ α β holes)
  : Component Γ α β holes :=
  { LocalState := ReactionState α body.LocalState, node := .onChange react body.node }

abbrev Component.collection
  {Γ : Context}
  {α β γ : Type}
  {views : Nat}
  (path : Path α (Collection β))
  (label : Computation Γ α String)
  (row : Presentation [] (Context.row β Γ) β γ views)
  (display : CollectionDisplay Γ α β views)
  : Component Γ α (List γ) (holes := 1) :=
  { LocalState := Std.HashMap Uuid row.LocalState, node := .collection path label row.node display }

abbrev Component.zoom?
  {Γ : Context}
  {α β γ : Type}
  {holes : Nat}
  (target : Computation Γ α (Option (PartialPath α β)))
  (body : Component Γ β γ holes)
  : Component Γ α (Option γ) holes :=
  { LocalState := body.LocalState, node := .zoom? target body.node }

abbrev Component.zoom
  {Γ : Context}
  {α β γ : Type}
  {holes : Nat}
  (path : Path α β)
  (body : Component Γ β γ holes)
  : Component Γ α γ holes :=
  { LocalState := body.LocalState, node := .zoom path body.node }

/-- Loaded subtree state persists while its resolved status is equal.
To keep state across statuses, observe `Component.loadStatus` instead. -/
abbrev Component.load
  {Γ : Context}
  {α β data : Type}
  {holes : Nat}
  [inst : DecidableEq data]
  (source : Computation Γ α (Source data))
  (body : Status data → Component Γ α β holes)
  : Component Γ α β holes :=
  { LocalState := LoadedState data (fun status => (body status).LocalState)
    node := .load source (fun status => (body status).node) }

def Component.visibleWhen
  {Γ : Context}
  {α β : Type}
  (condition : Computation Γ α Bool)
  (body : Component Γ α β)
  : Component Γ α β :=
  .withAvailability ((fun visible => if visible then .enabled else .hidden) <$> condition) body

def Component.disabledWhen
  {Γ : Context}
  {α β : Type}
  (condition : Computation Γ α Bool)
  (body : Component Γ α β)
  : Component Γ α β :=
  .withAvailability ((fun disabled => if disabled then .disabled else .enabled) <$> condition) body

abbrev Component.select
  {Γ : Context}
  {α β Key : Type}
  [DecidableEq Key]
  [Forms.Model.Key Key]
  (path : Path α β)
  (label : Computation Γ α String)
  (options : Computation Γ α (SelectOptions Key β))
  (selected : β → Key)
  : Component Γ α :=
  { LocalState := Unit
    node := .select (.path path) label options selected (.const OptionAvailability.always) }

abbrev Component.stateSelect
  {Γ : Context}
  {α β Key : Type}
  [DecidableEq Key]
  [Forms.Model.Key Key]
  (var : Var Γ β)
  (label : Computation Γ α String)
  (options : Computation Γ α (SelectOptions Key β))
  (selected : β → Key)
  : Component Γ α :=
  { LocalState := Unit
    node := .select (.var var) label options selected (.const OptionAvailability.always) }

abbrev Component.selectWithAvailability
  {Γ : Context}
  {α β Key : Type}
  [DecidableEq Key]
  [Forms.Model.Key Key]
  (path : Path α β)
  (label : Computation Γ α String)
  (options : Computation Γ α (SelectOptions Key β))
  (selected : β → Key)
  (availability : Computation Γ α (SelectOption Key β → OptionAvailability))
  : Component Γ α :=
  { LocalState := Unit, node := .select (.path path) label options selected availability }

abbrev Component.lookup
  {Γ : Context}
  {α Key Details : Type}
  [Lean.ToJson Key]
  (path : Path α (Option (Reference Key)))
  (label : Computation Γ α String)
  (search : Computation Γ α ((searchText : String) → Source (LookupResults Key Details)))
  (availability : Computation Γ α (LookupCandidate Key Details → OptionAvailability))
  : Component Γ α :=
  { LocalState := Option String, node := .lookup path label search availability }

structure Labelled (β : Type) where
  value : β
  label : String

def SelectOptions.ofValues
  {β : Type}
  [Constructors β]
  (options : List (Labelled β))
  (tags_nodup : (options.map (Constructors.tag ·.value)).Nodup)
  (labels_nodup : (options.map (·.label)).Nodup)
  : SelectOptions (Constructors.Tag β) β where
  options := options.map fun option =>
    { key := Constructors.tag option.value, label := option.label, start := option.value }
  keys_nodup := by simpa [List.map_map, Function.comp_def] using tags_nodup
  labels_nodup := by simpa [List.map_map, Function.comp_def] using labels_nodup

def Component.enum
  {Γ : Context}
  {α β : Type}
  [Constructors β]
  (path : Path α β)
  (label : Computation Γ α String)
  (options : List (Labelled β))
  (tags_nodup : (options.map (Constructors.tag ·.value)).Nodup := by decide)
  (labels_nodup : (options.map (·.label)).Nodup := by decide)
  : Component Γ α :=
  .select path label (.const (.ofValues options tags_nodup labels_nodup)) Constructors.tag

def Component.enumWithAvailability
  {Γ : Context}
  {α β : Type}
  [Constructors β]
  (path : Path α β)
  (label : Computation Γ α String)
  (options : List (Labelled β))
  (availability : Computation Γ α (β → OptionAvailability))
  (tags_nodup : (options.map (Constructors.tag ·.value)).Nodup := by decide)
  (labels_nodup : (options.map (·.label)).Nodup := by decide)
  : Component Γ α :=
  .selectWithAvailability path label (.const (.ofValues options tags_nodup labels_nodup))
    Constructors.tag ((fun available option => available option.start) <$> availability)

def Component.enumSet
  {Γ : Context}
  {α β : Type}
  [Constructors β]
  [DecidableEq β]
  (path : Path α { items : List β // items.Nodup })
  (label : Computation Γ α String)
  (options : List (Labelled β))
  (tags_nodup : (options.map (Constructors.tag ·.value)).Nodup := by decide)
  (labels_nodup : (options.map (·.label)).Nodup := by decide)
  : Component Γ α :=
  .field path label <|
    (Editor.choices (.ofValues options tags_nodup labels_nodup) Constructors.tag).subtype
      List.Nodup "Pick each option once."

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

/-- Outputs the status of `source`.
Unlike `Component.load`, an observer keeps its state across statuses. -/
def Component.loadStatus
  {Γ : Context}
  {α data : Type}
  [inst : DecidableEq data]
  (source : Computation Γ α (Source data))
  : Component Γ α (Status data) :=
  .load source fun status => .output (.const status)

abbrev Presentation.layouts
  {Δ : ViewContext}
  {Γ : Context}
  {α β : Type}
  {views : Nat}
  (output : Computation Γ α β)
  (arrangement : Computation Γ α (Vector (Layout Δ) views))
  : Presentation Δ Γ α β views :=
  { LocalState := Unit, node := .layout output arrangement }

abbrev Presentation.layout
  {Δ : ViewContext}
  {Γ : Context}
  {α β : Type}
  (output : Computation Γ α β)
  (arrangement : Computation Γ α (Layout Δ))
  : Presentation Δ Γ α β :=
  .layouts output ((#v[·]) <$> arrangement)

abbrev Presentation.arrange
  {Δ : ViewContext}
  {Γ : Context}
  {α : Type}
  (arrangement : Computation Γ α (Layout Δ))
  : Presentation Δ Γ α :=
  .layout (.const ()) arrangement

abbrev Presentation.own
  {Δ : ViewContext}
  {Γ : Context}
  {α β γ : Type}
  {holes views : Nat}
  (component : Component Γ α β holes)
  (body : Presentation (holes :: Δ) (⟨.readOnly, β⟩ :: Γ) α γ views)
  : Presentation Δ Γ α γ views :=
  { LocalState := ObservationState component.LocalState body.LocalState
    node := .own component.node body.node }

abbrev Presentation.bind
  {Δ : ViewContext}
  {Γ : Context}
  {α β γ : Type}
  {views : Nat}
  (initial : β)
  (body : Presentation Δ (⟨.writable, β⟩ :: Γ) α γ views)
  : Presentation Δ Γ α γ views :=
  { LocalState := Binding β body.LocalState, node := .bind initial body.node }

/-- Binds the active tab and owns its strip; `body` reads the tab as `.there .here` and places the
strip as `ViewRef.here`. -/
abbrev Presentation.tabs
  {Δ : ViewContext}
  {n : Nat}
  {Γ : Context}
  {α β : Type}
  (label : Computation (⟨.writable, Fin (n + 1)⟩ :: Γ) α String)
  (labels : Computation (⟨.writable, Fin (n + 1)⟩ :: Γ) α (Vector String (n + 1)))
  (body : Presentation (0 :: Δ) (⟨.readOnly, Unit⟩ :: ⟨.writable, Fin (n + 1)⟩ :: Γ) α β)
  : Presentation Δ Γ α β :=
  .bind 0 (.own (.tabBar label .here labels) body)

abbrev Component.present
  {Γ : Context}
  {α β : Type}
  (body : Presentation [] Γ α β)
  : Component Γ α β :=
  { LocalState := body.LocalState, node := .present body.node }

abbrev Component.bind
  {Γ : Context}
  {α β γ : Type}
  (initial : β)
  (body : Component (⟨.writable, β⟩ :: Γ) α γ)
  : Component Γ α γ :=
  .present <|
    .bind initial <|
      .own body <|
        .layout { inputs := inputs[.ui .here], run := id } (.const (.place .here))

abbrev Component.rename
  {Γ Δ : Context}
  {α β : Type}
  {holes : Nat}
  (rename : Renaming Γ Δ)
  (component : Component Γ α β holes)
  : Component Δ α β holes :=
  { LocalState := component.LocalState, node := component.node.rename rename }

abbrev Component.weaken
  {Γ : Context}
  {entry : Entry}
  {α β : Type}
  {holes : Nat}
  (component : Component Γ α β holes)
  : Component (entry :: Γ) α β holes :=
  component.rename Renaming.shift

abbrev Layout.grouped
  {Δ : ViewContext}
  {Γ : Context}
  {α : Type}
  (label : Computation Γ α String)
  (placed : List (ViewRef Δ 0))
  : Computation Γ α (Layout Δ) :=
  (fun label => .group (some label) (placed.map Layout.place)) <$> label

/-- Owns `children` after the presentations in `placed`, then lays out all of them with `render`
applied to `arrangement`. -/
def Presentation.ownAll
  {Δ : ViewContext}
  {Γ Γ' : Context}
  {α β γ : Type}
  (rename : Renaming Γ Γ')
  (arrangement : Computation Γ' α γ)
  (render : {Δ : ViewContext} → γ → List (ViewRef Δ 0) → Layout Δ)
  (placed : List (ViewRef Δ 0))
  : List (Component Γ α β) → Presentation Δ Γ' α
  | [] => .arrange ((render · placed) <$> arrangement)
  | child :: rest =>
    .own (child.rename rename) <|
      Presentation.ownAll (fun ref => .there (rename ref)) (arrangement.rename Renaming.shift)
        render (placed.map ViewRef.there ++ [.here]) rest

/-- Owns `cell` innermost in `cells` and places it after their views. -/
def PresentationNode.snoc
  {Δ : ViewContext}
  {Γ Γ' : Context}
  {α state β : Type}
  {views : Nat}
  (cells : PresentationNode Δ Γ' α state β views)
  (rename : Renaming Γ Γ')
  (cell : Component Γ α)
  : Presentation Δ Γ' α β (views + 1) :=
  match cells with
  | .layout output arrangement =>
    .own (cell.rename rename) <|
      .layouts (output.rename Renaming.shift)
        ((fun layouts => (layouts.map (Layout.rename ViewRef.there)).push (.place .here)) <$>
          arrangement.rename Renaming.shift)
  | .own component body =>
    .own { LocalState := _, node := component } (body.snoc (fun ref => .there (rename ref)) cell)
  | .bind initial body => .bind initial (body.snoc (fun ref => .there (rename ref)) cell)

def PresentationNode.group
  {Δ : ViewContext}
  {Γ Γ' : Context}
  {α state β : Type}
  {views : Nat}
  (cells : PresentationNode Δ Γ' α state β views)
  (rename : Renaming Γ Γ')
  (label : Computation Γ α String)
  : PresentationNode Δ Γ' α state β 1 :=
  match cells with
  | .layout output arrangement =>
    .layout output
      ((fun label layouts => #v[.group (some label) layouts.toList]) <$> label.rename rename <*>
        arrangement)
  | .own component body => .own component (body.group (fun ref => .there (rename ref)) label)
  | .bind initial body => .bind initial (body.group (fun ref => .there (rename ref)) label)

abbrev Columns.nil {Γ : Context} {α : Type} : Columns Γ α :=
  { headers := #v[], cells := .layouts (.const ()) (.const #v[]) }

def Columns.snoc
  {Γ : Context}
  {α β : Type}
  (columns : Columns Γ α β)
  (header : String)
  (cell : Component Γ α)
  : Columns Γ α β :=
  { headers := columns.headers.push header, cells := columns.cells.node.snoc (fun ref => ref) cell }

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

abbrev Columns.rename
  {Γ Δ : Context}
  {α β : Type}
  (rename : Renaming Γ Δ)
  (columns : Columns Γ α β)
  : Columns Δ α β :=
  { headers := columns.headers
    cells := { LocalState := _, node := columns.cells.node.rename rename } }

def Columns.group
  {Γ : Context}
  {α β : Type}
  (label : Computation Γ α String)
  (columns : Columns Γ α β)
  : Component Γ α β :=
  { LocalState := _, node := .present (columns.cells.node.group (fun ref => ref) label) }

/-- Renders `producer` followed by `body`.
The first entry in `body`'s context is the producer's current output, available read-only. -/
abbrev Component.observe
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

/-- A status marker for the reports at `path`. -/
abbrev Component.statusMarkerAt
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  : Component Γ α :=
  .observe (.reports path) (.statusMarker { inputs := inputs[.ui .here], run := id })

abbrev Component.sequence
  {Γ : Context}
  {α β : Type}
  (first : Component Γ α Unit)
  (second : Component Γ α β)
  : Component Γ α β :=
  .observe first second.weaken

abbrev Component.withOutput
  {Γ : Context}
  {α β : Type}
  (view : Component Γ α)
  (output : Computation Γ α β)
  : Component Γ α β :=
  .sequence view (.output output)

abbrev Component.void
  {Γ : Context}
  {α β : Type}
  (body : Component Γ α β)
  : Component Γ α :=
  .present (.own body (.arrange (.const (.place .here))))

abbrev Component.withAddButton
  {Γ : Context}
  {α β γ : Type}
  (path : Path α (Collection β))
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
abbrev Computation.numbered
  {Γ : Context}
  {β : Type}
  (itemLabel : String)
  : Computation (Context.row β Γ) β String :=
  { inputs := inputs[.ui Ref.row], run := fun row => s!"{itemLabel} {row.index.val + 1}" }

abbrev Component.list
  {Γ : Context}
  {α β γ : Type}
  (path : Path α (Collection β))
  (label : Computation Γ α String)
  (rowLabel : Computation (Context.row β Γ) β String)
  (addCaption : Computation Γ α String)
  (initial : β)
  (body : Component Γ β γ)
  : Component Γ α (List γ) :=
  let rowLabel := rowLabel.rename fun ref => .there (.there ref)
  .withAddButton path addCaption initial <|
    .collection path label
      (.own (body.rename Renaming.row) <|
        .own (.button "Remove" (.set (.there Ref.rowRemoved) (.const true))) <|
          .layout { inputs := inputs[.ui (Ref.there Ref.here)], run := id }
            ((fun label => .group (some label) [.place (.there .here), .place .here]) <$> rowLabel))
      .list

abbrev Component.table
  {Γ : Context}
  {α β γ : Type}
  (path : Path α (Collection β))
  (label : Computation Γ α String)
  (rowLabel : Computation (Context.row β Γ) β String)
  (addCaption : Computation Γ α String)
  (initial : β)
  (columns : Columns Γ β γ)
  (selection : Option (Var Γ RowSelection) := none)
  : Component Γ α (List γ) :=
  let removeRow : Action (Context.row β Γ) β := .set Ref.rowRemoved (.const true)
  let isSelected (selection : Var (Context.row β Γ) RowSelection)
      : Computation (Context.row β Γ) β Bool :=
    { inputs := inputs[.ui selection, .ui Ref.row]
      run := fun current row => current == .of row.current }
  let actions : Component (Context.row β Γ) β := match selection with
    | none => .button "Remove" removeRow
    | some selection =>
      let selection := Renaming.row selection
      .sequence
        (.button ((if · then "Selected" else "Select") <$> isSelected selection)
          (.set selection { inputs := inputs[.ui Ref.row], run := fun row => .of row.current }))
        (.button "Remove" <|
          .set selection
            { inputs := inputs[.ui selection, .ui Ref.row]
              run := fun current row => if current == .of row.current then .none else current }
          ++ removeRow)
  let selected := selection.map (isSelected ∘ Renaming.row)
  let columns := (columns.rename Renaming.row).snoc "Actions" actions
  .withAddButton path addCaption initial <|
    .collection path label columns.cells (.table (.const columns.headers) rowLabel selected)

abbrev Component.labeled
  {Γ : Context}
  {α β : Type}
  (label : Computation Γ α String)
  (body : Component Γ α β)
  : Component Γ α β :=
  .present <|
    .own body <|
      .layout { inputs := inputs[.ui .here], run := id }
        (Layout.grouped (label.rename Renaming.shift) [.here])

def Component.group
  {Γ : Context}
  {α : Type}
  (label : Computation Γ α String)
  (children : List (Component Γ α))
  : Component Γ α :=
  .present <|
    Presentation.ownAll (fun ref => ref) label
      (fun label placed => .group (some label) (placed.map .place)) [] children

def Component.choice
  {Γ : Context}
  {α β : Type}
  [Constructors β]
  [LawfulConstructors β]
  (path : Path α β)
  (label : Computation Γ α String)
  (branches : List (Branch Γ β))
  (tags_nodup : (branches.map (Constructors.tagOf ·.constructor)).Nodup := by simp <;> decide)
  (labels_nodup : (branches.map (·.label)).Nodup := by simp <;> decide)
  : Component Γ α :=
  let options : SelectOptions _ β := {
    options := branches.map fun branch => {
      key := Constructors.tagOf branch.constructor
      label := branch.label
      start := Constructors.inject branch.constructor branch.initial }
    keys_nodup := by simpa [List.map_map, Function.comp_def] using tags_nodup
    labels_nodup := by simpa [List.map_map, Function.comp_def] using labels_nodup }
  let bodies := branches.map fun branch =>
    let target := (PartialPath.ofPath path).trans (.constructor branch.constructor .self)
    Component.zoom? (.const (some target)) branch.body
  .present <|
    .own (.select path label (.const options) Constructors.tag) <|
      Presentation.ownAll Renaming.shift { inputs := inputs[path], run := Constructors.tag }
        (fun tag placed => match placed with
          | [] => .group none []
          | selector :: bodies =>
            match (bodies.zip branches).find? (Constructors.tagOf ·.2.constructor == tag) with
            | none => .place selector
            | some (body, _) => .group none [.place selector, .place body])
        [.here] bodies

/-- A choice between no value, labelled `absent`, and a value edited by `body`. -/
def Component.optional
  {Γ : Context}
  {α β : Type}
  (path : Path α (Option β))
  (label : Computation Γ α String)
  (absent present : String)
  (initial : β)
  (body : Component Γ β)
  (distinct : absent ≠ present := by decide)
  : Component Γ α :=
  .choice path label
    (branches := [
      { constructor := OptionConstructor.none
        label := absent
        initial := ()
        body := .output (.const ()) },
      { constructor := OptionConstructor.some
        label := present
        initial
        body }])
    (tags_nodup := by simp [Constructors.tagOf])
    (labels_nodup := by simpa using distinct)

end Forms.Model
