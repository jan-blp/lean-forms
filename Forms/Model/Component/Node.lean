module

public import Forms.Model.Action
public import Forms.Model.Evidence
public import Forms.Model.Format
public import Forms.Model.Lookup
public import Forms.Model.PartialPath
public import Forms.Model.Target
public import Forms.Model.Select
public import Forms.Model.Component.State
public import Forms.Model.Component.Layout
public import Std.Data.HashMap

@[expose] public section
namespace Forms.Model

inductive Editor : Type → Type 1 where
  | formatted {α : Type} (format : Format α) : Editor α
  | checkbox : Editor Bool
  | choices {β Key : Type}
      [key : Forms.Model.Key Key]
      (options : SelectOptions Key β)
      (selected : β → Key)
      : Editor (List β)
  | refine {α β : Type}
      (editor : Editor α)
      (print : β → α)
      (parse : α → Except String β)
      (parse_print : ∀ value, parse (print value) = .ok value)
      : Editor β
  | whileTyping {α : Type} (editor : Editor α) : Editor α

abbrev Editor.text : Editor String := .formatted .plain

abbrev Editor.natural : Editor Nat := .formatted .natural

abbrev Editor.integer : Editor Int := .formatted .integer

abbrev Editor.int32 : Editor Int32 := .formatted .int32

abbrev Editor.int64 : Editor Int64 := .formatted .int64

abbrev Editor.decimal : Editor Decimal := .formatted .decimal

abbrev Editor.date : Editor Std.Time.PlainDate := .formatted .date

abbrev Editor.uuid : Editor Uuid := .formatted .uuid

def Editor.subtype
    {α : Type}
    (editor : Editor α)
    (property : α → Prop)
    [DecidablePred property]
    (errorMsg : String)
    : Editor { value : α // property value } :=
  editor.refine Subtype.val
    (fun value => if valid : property value then .ok ⟨value, valid⟩ else .error errorMsg)
    (fun value => by simp [value.property])

abbrev Editor.optional
    {α : Type}
    (format : Format α)
    (blank : (format.parse "").isOk = false := by decide)
    : Editor (Option α) :=
  .formatted (format.optional blank)

inductive Availability where
  | enabled
  | hidden
  | disabled
  deriving DecidableEq, Repr

inductive CollectionDisplay (Γ : Context) (α β : Type) : (columns : Nat) → Type 1 where
  | list : CollectionDisplay Γ α β 1
  | table {columns : Nat}
      (headers : Computation Γ α (Vector String columns))
      (rowLabel : Computation (Context.row β Γ) β String)
      (selected : Option (Computation (Context.row β Γ) β Bool))
      : CollectionDisplay Γ α β columns

structure EvidenceSlot (α β : Type) where
  path : Path α (Option Evidence)
  read : String → Except String β

inductive FieldEvidence {Γ : Context} {α β : Type} : Target Γ α β → Type 1 where
  | none {target : Target Γ α β} : FieldEvidence target
  | recordedAt {path : Path α β} (slot : EvidenceSlot α β) : FieldEvidence (.path path)

mutual
inductive ComponentNode : (Γ : Context) → (model state output : Type) → (holes : Nat) → Type 1 where
  /-- `evidence` records the document cells a value was picked from. -/
  | field {Γ : Context}
      {α β : Type}
      (target : Target Γ α β)
      (label : Computation Γ α String)
      (editor : Editor β)
      (evidence : FieldEvidence target)
      : ComponentNode Γ α Unit Unit 0
  | computed {Γ : Context}
      {α : Type}
      (label : Computation Γ α String)
      (value : Computation Γ α String)
      : ComponentNode Γ α Unit Unit 0
  | button {Γ : Context}
      {α : Type}
      (caption : Computation Γ α String)
      (action : Action Γ α)
      : ComponentNode Γ α Unit Unit 0
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
  | onChange {Γ : Context}
      {α β state : Type}
      {holes : Nat}
      (update : α → α → α)
      (body : ComponentNode Γ α state β holes)
      : ComponentNode Γ α state β holes
  /-- A choice among `options` for the value at `target`.
  The option with key `selected value` is marked selected, if there is one.
  Choosing a different option sets the value to its `start`; `availability` can refuse it. -/
  | select {Γ : Context}
      {α β Key : Type}
      [decidableEq : DecidableEq Key]
      [key : Forms.Model.Key Key]
      (target : Target Γ α β)
      (label : Computation Γ α String)
      (options : Computation Γ α (SelectOptions Key β))
      (selected : β → Key)
      (availability : Computation Γ α (SelectOption Key β → OptionAvailability))
      : ComponentNode Γ α Unit Unit 0
  | lookup {Γ : Context}
      {α Key Details : Type}
      [toJson : Lean.ToJson Key]
      (path : Path α (Option (Reference Key)))
      (label : Computation Γ α String)
      (search : Computation Γ α ((searchText : String) → Source (LookupResults Key Details)))
      (availability : Computation Γ α (LookupCandidate Key Details → OptionAvailability))
      : ComponentNode Γ α (Option String) Unit 0
  | output {Γ : Context}
      {α β : Type}
      (value : Computation Γ α β)
      : ComponentNode Γ α Unit β 0
  /-- Outputs the issues inside the `α` value this node receives, rendered or not; global issues
  are included only when that value is the whole model. -/
  | issues {Γ : Context}
      {α : Type}
      : ComponentNode Γ α Unit (List Issue) 0
  /-- Outputs the report messages targeting `path`. -/
  | reports {Γ : Context}
      {α β : Type}
      (path : Path α β)
      : ComponentNode Γ α Unit (List ReportMessage) 0
  /-- Shows `reports` as a status marker, or nothing when empty. -/
  | statusMarker {Γ : Context}
      {α : Type}
      (reports : Computation Γ α (List ReportMessage))
      : ComponentNode Γ α Unit Unit 0
  /-- Shows `row` for each entry at `path` as `display` says, then the content of its hole.
  A row edits its entry's content; its id is in the row context. Row state is kept by id. -/
  | collection {Γ : Context}
      {α β γ rowState : Type}
      {views : Nat}
      (path : Path α (Collection β))
      (label : Computation Γ α String)
      (row : PresentationNode [] (Context.row β Γ) β rowState γ views)
      (display : CollectionDisplay Γ α β views)
      : ComponentNode Γ α (Std.HashMap Uuid rowState) (List γ) 1
  | zoom? {Γ : Context}
      {α β γ state : Type}
      {holes : Nat}
      (target : Computation Γ α (Option (PartialPath α β)))
      (body : ComponentNode Γ β state γ holes)
      : ComponentNode Γ α state (Option γ) holes
  | zoom {Γ : Context}
      {α β γ state : Type}
      {holes : Nat}
      (path : Path α β)
      (body : ComponentNode Γ β state γ holes)
      : ComponentNode Γ α state γ holes
  | load {Γ : Context}
      {α β data : Type}
      {states : Status data → Type}
      {holes : Nat}
      [inst : DecidableEq data]
      (source : Computation Γ α (Source data))
      (body : (status : Status data) → ComponentNode Γ α (states status) β holes)
      : ComponentNode Γ α (LoadedState data states) β holes
  | present {Γ : Context}
      {α β state : Type}
      (body : PresentationNode [] Γ α state β 1)
      : ComponentNode Γ α state β 0

/-- Components owned in order, arranged into `views` views;
`Δ` gives the hole count of each view in scope. -/
inductive PresentationNode
  : (Δ : ViewContext)
  → (Γ : Context)
  → (model state output : Type)
  → (views : Nat)
  → Type 1 where
  | layout {Δ : ViewContext}
      {Γ : Context}
      {α β : Type}
      {views : Nat}
      (output : Computation Γ α β)
      (arrangement : Computation Γ α (Vector (Layout Δ) views))
      : PresentationNode Δ Γ α Unit β views
  /-- Owns `component`: `body` reads its output as `Ref.here` and places its view as `ViewRef.here`. -/
  | own {Δ : ViewContext}
      {Γ : Context}
      {α β γ ownedState bodyState : Type}
      {holes views : Nat}
      (component : ComponentNode Γ α ownedState β holes)
      (body : PresentationNode (holes :: Δ) (⟨.readOnly, β⟩ :: Γ) α bodyState γ views)
      : PresentationNode Δ Γ α (ObservationState ownedState bodyState) γ views
  | bind {Δ : ViewContext}
      {Γ : Context}
      {α β γ state : Type}
      {views : Nat}
      (initial : β)
      (body : PresentationNode Δ (⟨.writable, β⟩ :: Γ) α state γ views)
      : PresentationNode Δ Γ α (Binding β state) γ views

end

end Forms.Model
