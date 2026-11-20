module

public import Forms.Model.RowSelection
public import Forms.Model.Item
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

@[reducible] def Component.issues
  {Γ : Context}
  {α : Type}
  : Component Γ α (List Issue) :=
  { LocalState := Unit, node := .issues }

@[reducible] def Component.reports
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  : Component Γ α (List ReportMessage) :=
  ⟨Unit, .reports path⟩

@[reducible] def Component.statusMarker
  {Γ : Context}
  {α : Type}
  (reports : Computation Γ α (List ReportMessage))
  : Component Γ α :=
  ⟨Unit, .statusMarker reports⟩

def RowSelection.itemPath
  {α β : Type}
  [HasUuid β]
  (items : Path α (List β))
  : RowSelection → Option (PartialPath α β)
  | .none => Option.none
  | .row id => some ((PartialPath.ofPath items).trans (.item id .self))

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
  ⟨Unit, .field path label editor none⟩

@[reducible] def Component.fieldWithEvidence
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  (evidence : Path α (Option Evidence))
  (label : Computation Γ α String)
  (editor : Editor β)
  : Component Γ α :=
  ⟨Unit, .field path label editor (some evidence)⟩

@[reducible] def Component.computed
  {Γ : Context}
  {α : Type}
  (label : Computation Γ α String)
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

@[reducible] def Component.collection
  {Γ : Context}
  {α β γ : Type}
  {views : Nat}
  [HasUuid β]
  (path : Path α (List β))
  (label : Computation Γ α String)
  (row : Presentation [] (Context.row β Γ) β γ views)
  (display : CollectionDisplay Γ α β views)
  : Component Γ α (List γ) (holes := 1) :=
  ⟨Std.HashMap Uuid row.LocalState, .collection path label row.node display⟩

@[reducible] def Component.zoom?
  {Γ : Context}
  {α β γ : Type}
  {holes : Nat}
  (target : Computation Γ α (Option (PartialPath α β)))
  (body : Component Γ β γ holes)
  : Component Γ α (Option γ) holes :=
  ⟨body.LocalState, .zoom? target body.node⟩

@[reducible] def Component.zoom
  {Γ : Context}
  {α β γ : Type}
  {holes : Nat}
  (path : Path α β)
  (body : Component Γ β γ holes)
  : Component Γ α γ holes :=
  ⟨body.LocalState, .zoom path body.node⟩

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

@[reducible] def Component.select
  {Γ : Context}
  {α β κ : Type}
  [DecidableEq κ]
  [Key κ]
  (path : Path α β)
  (label : Computation Γ α String)
  (options : Computation Γ α (SelectOptions κ β))
  (selected : β → κ)
  : Component Γ α :=
  ⟨Unit, .select path label options selected⟩

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

@[reducible] def Presentation.layouts
  {Δ : ViewContext}
  {Γ : Context}
  {α β : Type}
  {views : Nat}
  (output : Computation Γ α β)
  (arrangement : Computation Γ α (Vector (Layout Δ) views))
  : Presentation Δ Γ α β views :=
  ⟨Unit, .layout output arrangement⟩

@[reducible] def Presentation.layout
  {Δ : ViewContext}
  {Γ : Context}
  {α β : Type}
  (output : Computation Γ α β)
  (arrangement : Computation Γ α (Layout Δ))
  : Presentation Δ Γ α β :=
  .layouts output ((#v[·]) <$> arrangement)

@[reducible] def Presentation.arrange
  {Δ : ViewContext}
  {Γ : Context}
  {α : Type}
  (arrangement : Computation Γ α (Layout Δ))
  : Presentation Δ Γ α :=
  .layout (.const ()) arrangement

@[reducible] def Presentation.own
  {Δ : ViewContext}
  {Γ : Context}
  {α β γ : Type}
  {holes views : Nat}
  (component : Component Γ α β holes)
  (body : Presentation (holes :: Δ) (⟨.readOnly, β⟩ :: Γ) α γ views)
  : Presentation Δ Γ α γ views :=
  ⟨ObservationState component.LocalState body.LocalState, .own component.node body.node⟩

@[reducible] def Presentation.bind
  {Δ : ViewContext}
  {Γ : Context}
  {α β γ : Type}
  {views : Nat}
  (initial : β)
  (body : Presentation Δ (⟨.writable, β⟩ :: Γ) α γ views)
  : Presentation Δ Γ α γ views :=
  ⟨Binding β body.LocalState, .bind initial body.node⟩

/-- Binds the active tab and owns its strip; `body` reads the tab as `.there .here` and places the
strip as `ViewRef.here`. -/
@[reducible] def Presentation.tabs
  {Δ : ViewContext}
  {n : Nat}
  {Γ : Context}
  {α β : Type}
  (label : Computation (⟨.writable, Fin (n + 1)⟩ :: Γ) α String)
  (labels : Computation (⟨.writable, Fin (n + 1)⟩ :: Γ) α (Vector String (n + 1)))
  (body : Presentation (0 :: Δ) (⟨.readOnly, Unit⟩ :: ⟨.writable, Fin (n + 1)⟩ :: Γ) α β)
  : Presentation Δ Γ α β :=
  .bind 0 (.own (.tabBar label .here labels) body)

@[reducible] def Component.present
  {Γ : Context}
  {α β : Type}
  (body : Presentation [] Γ α β)
  : Component Γ α β :=
  ⟨body.LocalState, .present body.node⟩

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

@[reducible] def Component.weaken
  {Γ : Context}
  {entry : Entry}
  {α β : Type}
  {holes : Nat}
  (component : Component Γ α β holes)
  : Component (entry :: Γ) α β holes :=
  component.rename Renaming.shift

@[reducible] def Layout.grouped
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
  | .own component body => .own ⟨_, component⟩ (body.snoc (fun ref => .there (rename ref)) cell)
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

@[reducible] def Columns.nil {Γ : Context} {α : Type} : Columns Γ α :=
  ⟨#v[], .layouts (.const ()) (.const #v[])⟩

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

/-- A status marker for the reports at `path`. -/
@[reducible] def Component.statusMarkerAt
  {Γ : Context}
  {α β : Type}
  (path : Path α β)
  : Component Γ α :=
  .observe (.reports path) (.statusMarker { inputs := inputs[.ui .here], run := id })

@[reducible] def Component.sequence
  {Γ : Context}
  {α β : Type}
  (first : Component Γ α Unit)
  (second : Component Γ α β)
  : Component Γ α β :=
  .observe first second.weaken

@[reducible] def Component.withOutput
  {Γ : Context}
  {α β : Type}
  (view : Component Γ α)
  (output : Computation Γ α β)
  : Component Γ α β :=
  .sequence view (.output output)

@[reducible] def Component.void
  {Γ : Context}
  {α β : Type}
  (body : Component Γ α β)
  : Component Γ α :=
  .present (.own body (.arrange (.const (.place .here))))

@[reducible] def Component.withAddButton
  {Γ : Context}
  {α β γ : Type}
  [HasUuid β]
  (path : Path α (List β))
  (caption : Computation Γ α String)
  (initial : HasUuid.WithoutUuid β)
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

@[reducible] def Component.list
  {Γ : Context}
  {α β γ : Type}
  [HasUuid β]
  (path : Path α (List β))
  (label : Computation Γ α String)
  (rowLabel : Computation (Context.row β Γ) β String)
  (addCaption : Computation Γ α String)
  (initial : HasUuid.WithoutUuid β)
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

@[reducible] def Component.table
  {Γ : Context}
  {α β γ : Type}
  [HasUuid β]
  (path : Path α (List β))
  (label : Computation Γ α String)
  (rowLabel : Computation (Context.row β Γ) β String)
  (addCaption : Computation Γ α String)
  (initial : HasUuid.WithoutUuid β)
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
