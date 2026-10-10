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

end

end Forms
