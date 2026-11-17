module

public import Forms.Model.Computation

@[expose] public section
namespace Forms.Model

/-- A type-preserving affine traversal represented as an inspectable path to zero or one value.
Items are found by id, so it is only lawful for edits that keep item ids. -/
inductive PartialPath : Type → Type → Type 1 where
  | self {α : Type} : PartialPath α α
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
  | item
      {α β : Type}
      [hasUuid : HasUuid α]
      (id : Uuid)
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
  | .field (fields := _) f rest => .field f (rest.trans second)
  | .constructor (constructors := _) (lawful := _) ctor rest =>
    .constructor ctor (rest.trans second)
  | .item (hasUuid := _) id rest => .item id (rest.trans second)

def PartialPath.erase {α β : Type} : PartialPath α β → ErasedLocation
  | .self => []
  | .field (fields := _) f rest => .field (Fields.key f) :: rest.erase
  | .constructor (constructors := _) (lawful := _) ctor rest =>
    .constructor (Constructors.key ctor) :: rest.erase
  | .item (hasUuid := _) id rest => .item id :: rest.erase

def PartialPath.get?
  {α β : Type}
  (path : PartialPath α β)
  (value : α)
  : Option β :=
  match path with
  | .self => some value
  | .field (fields := _) f rest => rest.get? (Fields.get f value)
  | .constructor (constructors := _) (lawful := _) ctor rest =>
    (Constructors.project ctor value).bind rest.get?
  | .item (hasUuid := _) id rest =>
    match value.findIdx? (HasUuid.id · == id) with
    | none => none
    | some position => value[position]?.bind rest.get?

def PartialPath.set
  {α β : Type}
  (path : PartialPath α β)
  (new : β)
  (value : α)
  : α :=
  match path with
  | .self => new
  | .field (fields := _) f rest => Fields.set f (rest.set new (Fields.get f value)) value
  | .constructor (constructors := _) (lawful := _) ctor rest =>
    match Constructors.project ctor value with
    | none => value
    | some child => Constructors.inject ctor (rest.set new child)
  | .item (hasUuid := _) id rest =>
    match value.findIdx? (HasUuid.id · == id) with
    | none => value
    | some position => value.modify position (rest.set new)

end Forms.Model
