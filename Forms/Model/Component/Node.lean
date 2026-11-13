module

public import Forms.Model.Action
public import Forms.Model.PartialPath
public import Forms.Model.RowSelection
public import Forms.Model.Component.State

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

/-- Ordinary component views or a fixed set of table cells. -/
inductive Layout where
  | block
  | cells

@[reducible] def Layout.Headers : Layout → Type
  | .block => Unit
  | .cells => List String

def Layout.emptyHeaders : (layout : Layout) → layout.Headers
  | .block => ()
  | .cells => []

def Layout.appendHeaders : (layout : Layout) → layout.Headers → layout.Headers → layout.Headers
  | .block, _, _ => ()
  | .cells, first, second => first ++ second

mutual
inductive ComponentNode : (layout : Layout) → layout.Headers → Context → Type → Type → Type → Type 1 where
  | field {Γ : Context}
      {α β : Type}
      (path : Path α β)
      (label : String)
      (editor : Editor β)
      : ComponentNode .block () Γ α Unit Unit
  | computed {Γ : Context}
      {α : Type}
      (label : String)
      (value : Computation Γ α String)
      : ComponentNode .block () Γ α Unit Unit
  | button {Γ : Context}
      {α : Type}
      (label : String)
      (action : Action Γ α)
      : ComponentNode .block () Γ α Unit Unit
  | groupOf {Γ : Context}
      {α state : Type}
      (label : String)
      (children : ComponentsNode Γ α state)
      : ComponentNode .block () Γ α state Unit
  | labeled {Γ : Context}
      {α β state : Type}
      (label : String)
      (body : ComponentNode .block () Γ α state β)
      : ComponentNode .block () Γ α state β
  | withAvailability {layout : Layout}
      {headers : layout.Headers}
      {Γ : Context}
      {α β state : Type}
      (availability : Computation Γ α Availability)
      (body : ComponentNode layout headers Γ α state β)
      : ComponentNode layout headers Γ α state β
  | choiceOf {Γ : Context}
      {α β state : Type}
      (path : Path α β)
      (label : String)
      (branches : BranchesNode Γ β state)
      : ComponentNode .block () Γ α state Unit
  | mapOutput {layout : Layout}
      {headers : layout.Headers}
      {Γ : Context}
      {α β γ state : Type}
      (f : β → γ)
      (body : ComponentNode layout headers Γ α state β)
      : ComponentNode layout headers Γ α state γ
  | output {layout : Layout}
      {Γ : Context}
      {α β : Type}
      (value : Computation Γ α β)
      : ComponentNode layout layout.emptyHeaders Γ α Unit β
  | sequence {layout : Layout}
      {firstHeaders secondHeaders : layout.Headers}
      {Γ : Context}
      {α β firstState secondState : Type}
      (first : ComponentNode layout firstHeaders Γ α firstState Unit)
      (second : ComponentNode layout secondHeaders Γ α secondState β)
      : ComponentNode layout (layout.appendHeaders firstHeaders secondHeaders) Γ α (Binding firstState secondState) β
  | bind {layout : Layout}
      {headers : layout.Headers}
      {Γ : Context}
      {α β γ state : Type}
      (initial : β)
      (body : ComponentNode layout headers (⟨.writable, β⟩ :: Γ) α state γ)
      : ComponentNode layout headers Γ α (Binding β state) γ
  /-- Evaluates `producer` and exposes its output read-only to `body`. -/
  | observe {layout : Layout}
      {producerHeaders consumerHeaders : layout.Headers}
      {Γ : Context}
      {α β γ producerState consumerState : Type}
      (producer : ComponentNode layout producerHeaders Γ α producerState β)
      (body : ComponentNode layout consumerHeaders (⟨.readOnly, β⟩ :: Γ) α consumerState γ)
      : ComponentNode layout (layout.appendHeaders producerHeaders consumerHeaders) Γ α
          (ObservationState producerState consumerState) γ
  | collection {layout : Layout}
      {headers : layout.Headers}
      {Γ : Context}
      {α β γ state : Type}
      (path : Path α (List β))
      (label itemLabel : String)
      (initial : β)
      (body : ComponentNode layout headers Γ β state γ)
      (selection : Option (Var Γ RowSelection) := none)
      : ComponentNode .block () Γ α (List state) (List γ)
  | focus {layout : Layout}
      {headers : layout.Headers}
      {Γ : Context}
      {α β γ state : Type}
      (target : Computation Γ α (PartialPath α β))
      (body : ComponentNode layout headers Γ β state γ)
      : ComponentNode layout headers Γ α state (Option γ)
  | load {layout : Layout}
      {headers : layout.Headers}
      {Γ : Context}
      {α β data : Type}
      {states : Status data → Type}
      [inst : DecidableEq data]
      (source : Computation Γ α (Source data))
      (body : (status : Status data) → ComponentNode layout headers Γ α (states status) β)
      : ComponentNode layout headers Γ α (LoadedState data states) β
  | cell {Γ : Context}
      {α β state : Type}
      (header : String)
      (body : ComponentNode .block () Γ α state β)
      : ComponentNode .cells [header] Γ α state β

inductive ComponentsNode : Context → Type → Type → Type 1 where
  | nil {Γ : Context} {α : Type} : ComponentsNode Γ α Unit
  | cons {Γ : Context}
      {α headState tailState : Type}
      (head : ComponentNode .block () Γ α headState Unit)
      (tail : ComponentsNode Γ α tailState)
      : ComponentsNode Γ α (Binding headState tailState)
  | columns {Γ : Context}
      {α state : Type}
      {headers : List String}
      (columns : ComponentNode .cells headers Γ α state Unit)
      : ComponentsNode Γ α state

inductive BranchNode : Context → Type → Type → Type 1 where
  | mk {Γ : Context}
      {α β state : Type}
      (key label : String)
      (inject : β → α)
      (project : α → Option β)
      (initial : β)
      (body : ComponentNode .block () Γ β state Unit)
      : BranchNode Γ α state

inductive BranchesNode : Context → Type → Type → Type 1 where
  | nil {Γ : Context} {α : Type} : BranchesNode Γ α Unit
  | cons {Γ : Context}
      {α headState tailState : Type}
      (head : BranchNode Γ α headState)
      (tail : BranchesNode Γ α tailState)
      : BranchesNode Γ α (Binding headState tailState)
end

end Forms.Model
