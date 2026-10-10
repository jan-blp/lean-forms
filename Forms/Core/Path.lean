import Forms.Core.DataType

namespace Forms

inductive Path : (root : DataType) → (target : DataType) → Type 1 where
  | self {t : DataType} : Path t t
  | field
      {fieldNames : Enum} {fieldTypes : fieldNames → DataType} {target : DataType}
      (fieldName : fieldNames)
      (rest : Path (fieldTypes fieldName) target)
      : Path (.record fieldNames fieldTypes) target

section

variable {root target a b c : DataType}

def Path.get {root target}
    (path : Path root target)
    (value : DataType.denote root)
    : DataType.denote target :=
  match path with
  | .self => value
  | .field fieldName rest => Path.get rest (value fieldName)

def Path.set {root target}
    (path : Path root target)
    (replacement : DataType.denote target)
    (value : DataType.denote root)
    : DataType.denote root :=
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

def Path.Labels {root target} (path : Path root target) : Type :=
  match path with
  | .self => String
  | .field _ rest => String × Path.Labels rest

def Path.Labels.toList {root target}
    {path : Path root target}
    (labels : Path.Labels path)
    : List String :=
  match path with
  | .self => [labels]
  | .field _ rest => labels.1 :: Path.Labels.toList (path := rest) labels.2

end

end Forms
