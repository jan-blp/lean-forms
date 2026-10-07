import Forms.Core.DataType

namespace Forms

inductive Path : (source : DataType) → (target : DataType) → Type where
  | self {type : DataType} : Path type type

def Path.get
    {source target : DataType}
    (path : Path source target)
    (value : ⟦source⟧)
    : ⟦target⟧ :=
  match path with
  | .self => value

def Path.set
    {source target : DataType}
    (path : Path source target)
    (replacement : ⟦target⟧)
    (_value : ⟦source⟧)
    : ⟦source⟧ :=
  match path with
  | .self => replacement

def Path.trans
    {a b c : DataType}
    (p1 : Path a b)
    (p2 : Path b c)
    : Path a c :=
  match p1 with
  | .self => p2

def Path.Labels {source target : DataType} (path : Path source target) : Type :=
  match path with
  | .self => String

def Path.Labels.toList
    {source target : DataType}
    {path : Path source target}
    (labels : Path.Labels path)
    : List String :=
  match path with
  | .self => [labels]

end Forms
