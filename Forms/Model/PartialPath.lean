module

public import Forms.Model.Computation

@[expose] public section
namespace Forms.Model

/-- A type-preserving affine traversal represented as an inspectable path to zero or one value. -/
inductive PartialPath : Type → Type → Type 1 where
  | self {α : Type} : PartialPath α α
  | empty {α β : Type} : PartialPath α β
  | field
      {α β γ : Type}
      [fields : Fields α]
      (f : Fields.Field α β)
      (rest : PartialPath β γ)
      : PartialPath α γ
  | constructor
      {α β γ : Type}
      [constructors : Constructors α]
      [lawful : LawfulConstructors α]
      (ctor : Constructors.Constructor α β)
      (rest : PartialPath β γ)
      : PartialPath α γ
  | index
      {α β : Type}
      (position : Nat)
      (rest : PartialPath α β)
      : PartialPath (List α) β

def PartialPath.ofPath {α β : Type} : Path α β → PartialPath α β
  | .self => .self
  | .stepField (fields := _) f rest => .field f (.ofPath rest)

def PartialPath.trans
  {α β γ : Type}
  (first : PartialPath α β)
  (second : PartialPath β γ)
  : PartialPath α γ :=
  match first with
  | .self => second
  | .empty => .empty
  | .field (fields := _) f rest => .field f (rest.trans second)
  | .constructor (constructors := _) (lawful := _) ctor rest =>
    .constructor ctor (rest.trans second)
  | .index position rest => .index position (rest.trans second)

def PartialPath.get?
  {α β : Type}
  (path : PartialPath α β)
  (value : α)
  : Option β :=
  match path with
  | .self => some value
  | .empty => none
  | .field (fields := _) f rest => rest.get? (Fields.get f value)
  | .constructor (constructors := _) (lawful := _) ctor rest =>
    (Constructors.project ctor value).bind rest.get?
  | .index position rest => (value[position]?).bind rest.get?

def PartialPath.set
  {α β : Type}
  (path : PartialPath α β)
  (new : β)
  (value : α)
  : α :=
  match path with
  | .self => new
  | .empty => value
  | .field (fields := _) f rest => Fields.set f (rest.set new (Fields.get f value)) value
  | .constructor (constructors := _) (lawful := _) ctor rest =>
    match Constructors.project ctor value with
    | none => value
    | some child => Constructors.inject ctor (rest.set new child)
  | .index position rest =>
    match value[position]? with
    | none => value
    | some child => value.set position (rest.set new child)

end Forms.Model
