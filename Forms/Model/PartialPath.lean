module

public import Forms.Model.Computation

@[expose] public section
namespace Forms.Model

/-- A type-preserving affine traversal represented as an inspectable path to zero or one value. -/
inductive PartialPath : Type → Type → Type 1 where
  | self {value : Type} : PartialPath value value
  | empty {source target : Type} : PartialPath source target
  | field
      {source child target : Type}
      [Fields source]
      (f : Fields.Field source child)
      (rest : PartialPath child target)
      : PartialPath source target
  | constructor
      {source child target : Type}
      [Constructors source]
      [LawfulConstructors source]
      (ctor : Constructors.Constructor source child)
      (rest : PartialPath child target)
      : PartialPath source target
  | index
      {item target : Type}
      (position : Nat)
      (rest : PartialPath item target)
      : PartialPath (List item) target

def PartialPath.ofPath {source target : Type} : Path source target → PartialPath source target
  | .self => .self
  | @Path.stepField _ _ _ _inst f rest => .field f (.ofPath rest)

def PartialPath.trans
  {source middle target : Type}
  (first : PartialPath source middle)
  (second : PartialPath middle target)
  : PartialPath source target :=
  match first with
  | .self => second
  | .empty => .empty
  | @PartialPath.field _ _ _ _inst f rest => .field f (rest.trans second)
  | @PartialPath.constructor _ _ _ _inst _lawful ctor rest => .constructor ctor (rest.trans second)
  | .index position rest => .index position (rest.trans second)

def PartialPath.get?
  {source target : Type}
  (path : PartialPath source target)
  (value : source)
  : Option target :=
  match path with
  | .self => some value
  | .empty => none
  | @PartialPath.field _ _ _ _inst f rest => rest.get? (Fields.get f value)
  | @PartialPath.constructor _ _ _ _inst _lawful ctor rest => (Constructors.project ctor value).bind rest.get?
  | .index position rest => (value[position]?).bind rest.get?

def PartialPath.set
  {source target : Type}
  (path : PartialPath source target)
  (new : target)
  (value : source)
  : source :=
  match path with
  | .self => new
  | .empty => value
  | @PartialPath.field _ _ _ _inst f rest => Fields.set f (rest.set new (Fields.get f value)) value
  | @PartialPath.constructor _ _ _ _inst _lawful ctor rest =>
    match Constructors.project ctor value with
    | none => value
    | some child => Constructors.inject ctor (rest.set new child)
  | .index position rest =>
    match value[position]? with
    | none => value
    | some child => value.set position (rest.set new child)

end Forms.Model
