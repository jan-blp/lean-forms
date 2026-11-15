module

public import Forms.Model.Action
public import Forms.Model.PartialPath
public import Forms.Model.RowSelection
public import Forms.Model.Component.State
public import Forms.Model.Component.Layout

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

/-- An option of `select`, identified by `key`. -/
structure SelectOption (κ α : Type) where
  key : κ
  label : String
  start : α

/-- Options of `select`, with distinct keys and distinct labels. -/
structure SelectOptions (κ α : Type) where
  options : List (SelectOption κ α)
  keys_nodup : options.map SelectOption.key |>.Nodup := by simp <;> decide
  labels_nodup : options.map SelectOption.label |>.Nodup := by simp <;> decide

mutual
inductive ComponentNode : (Γ : Context) → (model state output : Type) → (holes : Nat) → Type 1 where
  | field {Γ : Context}
      {α β : Type}
      (path : Path α β)
      (label : Computation Γ α String)
      (editor : Editor β)
      : ComponentNode Γ α Unit Unit 0
  | computed {Γ : Context}
      {α : Type}
      (label : String)
      (value : Computation Γ α String)
      : ComponentNode Γ α Unit Unit 0
  | button {Γ : Context}
      {α : Type}
      (caption : Computation Γ α String)
      (action : Action Γ α)
      : ComponentNode Γ α Unit Unit 0
  /-- Tabs that set `active` to the chosen tab. -/
  | tabBar {Γ : Context}
      {α : Type}
      {n : Nat}
      (label : Computation Γ α String)
      (active : Var Γ (Fin n))
      (tabs : Computation Γ α (Vector String n))
      : ComponentNode Γ α Unit Unit 0
  | withAvailability {Γ : Context}
      {α β state : Type}
      {holes : Nat}
      (availability : Computation Γ α Availability)
      (body : ComponentNode Γ α state β holes)
      : ComponentNode Γ α state β holes
  /-- A choice among `options` for the value at `path`.
  The option with key `selected value` is marked selected, if there is one.
  Choosing a different option sets the value to its `start`. -/
  | select {Γ : Context}
      {α β κ : Type}
      [decidableEq : DecidableEq κ]
      [key : Key κ]
      (path : Path α β)
      (label : Computation Γ α String)
      (options : Computation Γ α (SelectOptions κ β))
      (selected : β → κ)
      : ComponentNode Γ α Unit Unit 0
  | output {Γ : Context}
      {α β : Type}
      (value : Computation Γ α β)
      : ComponentNode Γ α Unit β 0
  /-- Shows `row` for each item at `path`, then the content of its hole.
  Each row reads `Ref.row` and sets `Ref.rowRemoved` to remove itself. -/
  | list {Γ : Context}
      {α β γ rowState : Type}
      (path : Path α (List β))
      (label : Computation Γ α String)
      (row : ComponentNode (Context.row β Γ) β rowState γ 0)
      : ComponentNode Γ α (List rowState) (List γ) 1
  /-- Like `list`, with each row's views as cells under `headers` and its hole in the footer;
  `selection` marks its row and follows removals. -/
  | table {Γ : Context}
      {α β γ rowState : Type}
      {columns : Nat}
      (path : Path α (List β))
      (label : Computation Γ α String)
      (headers : Computation Γ α (Vector String columns))
      (rowLabel : Computation (Context.row β Γ) β String)
      (row : PresentationNode [] (Context.row β Γ) β rowState γ columns)
      (selection : Option (Var Γ RowSelection))
      : ComponentNode Γ α (List rowState) (List γ) 1
  | focus {Γ : Context}
      {α β γ state : Type}
      {holes : Nat}
      (target : Computation Γ α (PartialPath α β))
      (body : ComponentNode Γ β state γ holes)
      : ComponentNode Γ α state (Option γ) holes
  | load {Γ : Context}
      {α β data : Type}
      {states : Status data → Type}
      {holes : Nat}
      [inst : DecidableEq data]
      (source : Computation Γ α (Source data))
      (body : (status : Status data) → ComponentNode Γ α (states status) β holes)
      : ComponentNode Γ α (LoadedState data states) β holes
  /-- Owns components and places their views with a layout. -/
  | present {Γ : Context}
      {α β state : Type}
      (body : PresentationNode [] Γ α state β 1)
      : ComponentNode Γ α state β 0

/-- Components owned in order, arranged into `views` views;
`slots` gives the hole count of each slot in scope. -/
inductive PresentationNode
  : (slots : List Nat)
  → (Γ : Context)
  → (model state output : Type)
  → (views : Nat)
  → Type 1 where
  | layout {slots : List Nat}
      {Γ : Context}
      {α β : Type}
      {views : Nat}
      (output : Computation Γ α β)
      (arrangement : Computation Γ α (Vector (Layout slots) views))
      : PresentationNode slots Γ α Unit β views
  /-- Evaluates `component`, exposing its output to `body` and its view as `Slot.here`. -/
  | own {slots : List Nat}
      {Γ : Context}
      {α β γ ownedState bodyState : Type}
      {holes views : Nat}
      (component : ComponentNode Γ α ownedState β holes)
      (body : PresentationNode (holes :: slots) (⟨.readOnly, β⟩ :: Γ) α bodyState γ views)
      : PresentationNode slots Γ α (ObservationState ownedState bodyState) γ views
  | bind {slots : List Nat}
      {Γ : Context}
      {α β γ state : Type}
      {views : Nat}
      (initial : β)
      (body : PresentationNode slots (⟨.writable, β⟩ :: Γ) α state γ views)
      : PresentationNode slots Γ α (Binding β state) γ views

end

end Forms.Model
