import Forms.Core.DataType

namespace Forms

inductive Path : (source : DataType) → (target : DataType) → Type 1 where
  | self {t : DataType} : Path t t
  | field
      {fieldNames : Enum} {fieldTypes : fieldNames → DataType} {target : DataType}
      (fieldName : fieldNames)
      (rest : Path (fieldTypes fieldName) target)
      : Path (.record fieldNames fieldTypes) target

section

variable {source target a b c : DataType}

def Path.get {source target}
    (path : Path source target)
    (value : ⟦source⟧)
    : ⟦target⟧ :=
  match path with
  | .self => value
  | .field fieldName rest => Path.get rest (value fieldName)

def Path.set {source target}
    (path : Path source target)
    (replacement : ⟦target⟧)
    (value : ⟦source⟧)
    : ⟦source⟧ :=
  match path with
  | .self => replacement
  | .field fieldName rest => Function.update value fieldName (Path.set rest replacement (value fieldName))

def Path.trans {a b c}
    (p1 : Path a b)
    (p2 : Path b c)
    : Path a c :=
  match p1 with
  | .self => p2
  | .field fieldName rest => .field fieldName (Path.trans rest p2)

def Path.Labels {source target} (path : Path source target) : Type :=
  match path with
  | .self => String
  | .field _ rest => String × Path.Labels rest

def Path.Labels.toList {source target}
    {path : Path source target}
    (labels : Path.Labels path)
    : List String :=
  match path with
  | .self => [labels]
  | .field _ rest => labels.1 :: Path.Labels.toList (path := rest) labels.2

inductive AffineTraversal : (source : DataType) → (target : DataType) → Type 1 where
  | self {t : DataType} : AffineTraversal t t
  | field
      {fieldNames : Enum} {fieldTypes : fieldNames → DataType} {target : DataType}
      (fieldName : fieldNames)
      (rest : AffineTraversal (fieldTypes fieldName) target)
      : AffineTraversal (.record fieldNames fieldTypes) target
  | item {element target : DataType}
      (index : Nat)
      (rest : AffineTraversal element target)
      : AffineTraversal (.list element) target
  | constructor
      {tags : Enum} {constructors : tags → DataType} {target : DataType}
      (tag : tags)
      (rest : AffineTraversal (constructors tag) target)
      : AffineTraversal (.sum tags constructors) target

def AffineTraversal.trans {a b c}
  (p1 : AffineTraversal a b)
  (p2 : AffineTraversal b c)
  : AffineTraversal a c :=
  match p1 with
  | .self => p2
  | .field fieldName rest => .field fieldName (AffineTraversal.trans rest p2)
  | .item index rest => .item index (AffineTraversal.trans rest p2)
  | .constructor tag rest => .constructor tag (AffineTraversal.trans rest p2)

def Path.toAffineTraversal {source target}
  (path : Path source target)
  : AffineTraversal source target :=
  match path with
  | .self => .self
  | .field fieldName rest => .field fieldName (Path.toAffineTraversal rest)

inductive Traversal : (source : DataType) → (target : DataType) → Type 1 where
  | self {t : DataType} : Traversal t t
  | field
      {fieldNames : Enum} {fieldTypes : fieldNames → DataType} {target : DataType}
      (fieldName : fieldNames)
      (rest : Traversal (fieldTypes fieldName) target)
      : Traversal (.record fieldNames fieldTypes) target
  | each {element target : DataType}
      (rest : Traversal element target)
      : Traversal (.list element) target
  | constructor {tags : Enum} {constructors : tags → DataType} {target : DataType}
      (tag : tags)
      (rest : Traversal (constructors tag) target)
      : Traversal (.sum tags constructors) target

structure Traversal.Target (source target : DataType) where
  path : AffineTraversal source target
  value : ⟦target⟧

def Traversal.targets {source target : DataType}
  (traversal : Traversal source target)
  (value : ⟦source⟧)
  : List (Traversal.Target source target) :=
  match traversal with
  | .self => [{ path := .self, value }]
  | .field fieldName rest =>
      (Traversal.targets rest (value fieldName)).map fun found =>
        { path := .field fieldName found.path, value := found.value }
  | .each rest =>
      value.zipIdx.flatMap fun item =>
        (Traversal.targets rest item.1).map fun found =>
          { path := .item item.2 found.path, value := found.value }
  | .constructor tag rest =>
      if h : value.tag = tag then
        (Traversal.targets rest (h ▸ value.payload)).map fun found =>
          { path := .constructor tag found.path, value := found.value }
      else []

end

end Forms
