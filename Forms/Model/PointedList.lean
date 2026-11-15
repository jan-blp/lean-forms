module

@[expose] public section
namespace Forms.Model

structure PointedList (α : Type) where
  items : List α
  index : Fin items.length

namespace PointedList

variable {α : Type}

def current (list : PointedList α) : α :=
  list.items[list.index]

def count (list : PointedList α) : Nat :=
  list.items.length

def isFirst (list : PointedList α) : Bool :=
  list.index.val == 0

def isLast (list : PointedList α) : Bool :=
  list.index.val + 1 == list.items.length

end PointedList

end Forms.Model
