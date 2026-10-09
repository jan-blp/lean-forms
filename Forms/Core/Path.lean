import Forms.Core.DataType

namespace Forms

inductive Path : (root : DataType) → (target : DataType) → Type 1 where
  | self {type : DataType} : Path type type

def Path.get
    {root target : DataType}
    (path : Path root target)
    (value : DataType.denote root)
    : DataType.denote target :=
  match path with
  | .self => value

def Path.set
    {root target : DataType}
    (path : Path root target)
    (replacement : DataType.denote target)
    (_value : DataType.denote root)
    : DataType.denote root :=
  match path with
  | .self => replacement

def Path.trans
    {a b c : DataType}
    (p1 : Path a b)
    (p2 : Path b c)
    : Path a c :=
  match p1 with
  | .self => p2

def Path.Labels {root target : DataType} (path : Path root target) : Type :=
  match path with
  | .self => String

def Path.Labels.toList
    {root target : DataType}
    {path : Path root target}
    (labels : Path.Labels path)
    : List String :=
  match path with
  | .self => [labels]

end Forms
