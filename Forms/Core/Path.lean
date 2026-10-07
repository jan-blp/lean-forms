import Forms.Core.DataType

namespace Forms

inductive Path : (root : DataType) → (target : DataType) → Type where
  | here {type : DataType} : Path type type
  | child
      {n : Nat} {children : Fin n → DataType} {target : DataType}
      (index : Fin n)
      (rest : Path (children index) target)
      : Path (.group children) target

def Path.get
    {root target : DataType}
    (path : Path root target)
    (value : DataType.denote root)
    : DataType.denote target :=
  match path with
  | .here => value
  | .child index rest => Path.get rest (value index)

def Path.set
    {root target : DataType}
    (path : Path root target)
    (replacement : DataType.denote target)
    (value : DataType.denote root)
    : DataType.denote root :=
  match path with
  | .here => replacement
  | .child index rest => Function.update value index (Path.set rest replacement (value index))

def Path.trans
    {a b c : DataType}
    (p1 : Path a b)
    (p2 : Path b c)
    : Path a c :=
  match p1 with
  | .here => p2
  | .child index rest => .child index (Path.trans rest p2)

def Path.Labels {root target : DataType} (path : Path root target) : Type :=
  match path with
  | .here => String
  | .child _ rest => String × Path.Labels rest

def Path.Labels.toList
    {root target : DataType}
    {path : Path root target}
    (labels : Path.Labels path)
    : List String :=
  match path with
  | .here => [labels]
  | .child _ rest => labels.1 :: Path.Labels.toList (path := rest) labels.2

end Forms
