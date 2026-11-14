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

mutual
inductive ComponentNode : (Γ : Context) → (model state output : Type) → Type 1 where
  | field {Γ : Context}
      {α β : Type}
      (path : Path α β)
      (label : Computation Γ α String)
      (editor : Editor β)
      : ComponentNode Γ α Unit Unit
  | computed {Γ : Context}
      {α : Type}
      (label : String)
      (value : Computation Γ α String)
      : ComponentNode Γ α Unit Unit
  | button {Γ : Context}
      {α : Type}
      (caption : Computation Γ α String)
      (action : Action Γ α)
      : ComponentNode Γ α Unit Unit
  /-- Tabs that set `active` to the chosen tab. -/
  | tabBar {Γ : Context}
      {α : Type}
      {n : Nat}
      (label : String)
      (active : Var Γ (Fin n))
      (tabs : Vector String n)
      : ComponentNode Γ α Unit Unit
  | groupOf {Γ : Context}
      {α state : Type}
      (label : String)
      (children : ComponentsNode Γ α state)
      : ComponentNode Γ α state Unit
  | labeled {Γ : Context}
      {α β state : Type}
      (label : String)
      (body : ComponentNode Γ α state β)
      : ComponentNode Γ α state β
  | withAvailability {Γ : Context}
      {α β state : Type}
      (availability : Computation Γ α Availability)
      (body : ComponentNode Γ α state β)
      : ComponentNode Γ α state β
  | choiceOf {Γ : Context}
      {α β state : Type}
      (path : Path α β)
      (label : String)
      (branches : BranchesNode Γ β state)
      : ComponentNode Γ α state Unit
  | void {Γ : Context}
      {α β state : Type}
      (body : ComponentNode Γ α state β)
      : ComponentNode Γ α state Unit
  | output {Γ : Context}
      {α β : Type}
      (value : Computation Γ α β)
      : ComponentNode Γ α Unit β
  | sequence {Γ : Context}
      {α β firstState secondState : Type}
      (first : ComponentNode Γ α firstState Unit)
      (second : ComponentNode Γ α secondState β)
      : ComponentNode Γ α (Binding firstState secondState) β
  | bind {Γ : Context}
      {α β γ state : Type}
      (initial : β)
      (body : ComponentNode (⟨.writable, β⟩ :: Γ) α state γ)
      : ComponentNode Γ α (Binding β state) γ
  /-- Evaluates `producer` and exposes its output read-only to `body`. -/
  | observe {Γ : Context}
      {α β γ producerState consumerState : Type}
      (producer : ComponentNode Γ α producerState β)
      (body : ComponentNode (⟨.readOnly, β⟩ :: Γ) α consumerState γ)
      : ComponentNode Γ α
          (ObservationState producerState consumerState) γ
  | list {Γ : Context}
      {α β γ state : Type}
      (path : Path α (List β))
      (label itemLabel : String)
      (initial : β)
      (body : ComponentNode Γ β state γ)
      : ComponentNode Γ α (List state) (List γ)
  | table {Γ : Context}
      {α β γ state : Type}
      {headers : List String}
      (path : Path α (List β))
      (label itemLabel : String)
      (initial : β)
      (columns : ColumnsNode headers Γ β state γ)
      (selection : Option (Var Γ RowSelection) := none)
      : ComponentNode Γ α (List state) (List γ)
  | focus {Γ : Context}
      {α β γ state : Type}
      (target : Computation Γ α (PartialPath α β))
      (body : ComponentNode Γ β state γ)
      : ComponentNode Γ α state (Option γ)
  | load {Γ : Context}
      {α β data : Type}
      {states : Status data → Type}
      [inst : DecidableEq data]
      (source : Computation Γ α (Source data))
      (body : (status : Status data) → ComponentNode Γ α (states status) β)
      : ComponentNode Γ α (LoadedState data states) β
  /-- Owns components and places their views with a layout. -/
  | present {Γ : Context}
      {α β state : Type}
      (body : PresentationNode 0 Γ α state β)
      : ComponentNode Γ α state β

/-- Components owned in order; `slots` counts the presentations in scope. -/
inductive PresentationNode
  : (slots : Nat)
  → (Γ : Context)
  → (model state output : Type)
  → Type 1 where
  | layout {slots : Nat}
      {Γ : Context}
      {α β : Type}
      (output : Computation Γ α β)
      (arrangement : Computation Γ α (Layout slots))
      : PresentationNode slots Γ α Unit β
  /-- Evaluates `component`, exposing its output to `body` and its view as `Slot.here`. -/
  | own {slots : Nat}
      {Γ : Context}
      {α β γ ownedState bodyState : Type}
      (component : ComponentNode Γ α ownedState β)
      (body : PresentationNode (slots + 1) (⟨.readOnly, β⟩ :: Γ) α bodyState γ)
      : PresentationNode slots Γ α (ObservationState ownedState bodyState) γ
  | bind {slots : Nat}
      {Γ : Context}
      {α β γ state : Type}
      (initial : β)
      (body : PresentationNode slots (⟨.writable, β⟩ :: Γ) α state γ)
      : PresentationNode slots Γ α (Binding β state) γ

/-- Named cells and their explicitly chosen row output. -/
inductive ColumnsNode
  : (headers : List String)
  → (Γ : Context)
  → (row state output : Type)
  → Type 1 where
  | output {Γ : Context}
      {α β : Type}
      (value : Computation Γ α β)
      : ColumnsNode [] Γ α Unit β
  | cons {Γ : Context}
      {α β cellState restState : Type}
      {headers : List String}
      (header : String)
      (cell : ComponentNode Γ α cellState Unit)
      (rest : ColumnsNode headers Γ α restState β)
      : ColumnsNode (header :: headers) Γ α (Binding cellState restState) β
  | observe {Γ : Context}
      {α β γ cellState restState : Type}
      {headers : List String}
      (header : String)
      (cell : ComponentNode Γ α cellState β)
      (rest : ColumnsNode headers (⟨.readOnly, β⟩ :: Γ) α restState γ)
      : ColumnsNode (header :: headers) Γ α (ObservationState cellState restState) γ
  | bind {Γ : Context}
      {α β γ state : Type}
      {headers : List String}
      (initial : β)
      (body : ColumnsNode headers (⟨.writable, β⟩ :: Γ) α state γ)
      : ColumnsNode headers Γ α (Binding β state) γ
  | focus {Γ : Context}
      {α β γ state : Type}
      {headers : List String}
      (target : Computation Γ α (PartialPath α β))
      (body : ColumnsNode headers Γ β state γ)
      : ColumnsNode headers Γ α state (Option γ)

inductive ComponentsNode : (Γ : Context) → (model state : Type) → Type 1 where
  | nil {Γ : Context} {α : Type} : ComponentsNode Γ α Unit
  | cons {Γ : Context}
      {α headState tailState : Type}
      (head : ComponentNode Γ α headState Unit)
      (tail : ComponentsNode Γ α tailState)
      : ComponentsNode Γ α (Binding headState tailState)
  | columns {Γ : Context}
      {α state : Type}
      {headers : List String}
      (columns : ColumnsNode headers Γ α state Unit)
      : ComponentsNode Γ α state

inductive BranchNode : (Γ : Context) → (model state : Type) → Type 1 where
  | mk {Γ : Context}
      {α β state : Type}
      (key label : String)
      (inject : β → α)
      (project : α → Option β)
      (initial : β)
      (body : ComponentNode Γ β state Unit)
      : BranchNode Γ α state

inductive BranchesNode : (Γ : Context) → (model state : Type) → Type 1 where
  | nil {Γ : Context} {α : Type} : BranchesNode Γ α Unit
  | cons {Γ : Context}
      {α headState tailState : Type}
      (head : BranchNode Γ α headState)
      (tail : BranchesNode Γ α tailState)
      : BranchesNode Γ α (Binding headState tailState)
end

end Forms.Model
