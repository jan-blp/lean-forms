import Forms.Core.Expr

namespace Forms

inductive Widget : (t : DataType) → Type 1 where
  | textInput : Widget .text
  | checkbox : Widget .boolean
  | naturalInput : Widget .natural
  | select {domain : Choice} : Widget (.choice domain)

inductive Form : (root : DataType) → (t : DataType) → Type 1 where
  | field {root t : DataType}
      (label : String) (widget : Widget t) : Form root t
  | group {root : DataType} {n : Nat} {children : Fin n → DataType}
      (label : String) (fields : (i : Fin n) → Form root (children i))
      : Form root (.group children)
  | list {root element : DataType}
      (label : String) (item : Form element element) (defaultItem : element.denote)
      : Form root (.list element)
  | visibleWhen {root t : DataType}
      (condition : Expr root .boolean) (body : Form root t) : Form root t

structure FieldRef where
  {t : DataType}
  widget : Widget t
  labels : List String
  indices : List Nat

def Form.fieldRefs {root t : DataType} (form : Form root t)
    (value : root.denote) (localValue : t.denote) : List FieldRef :=
  match form with
  | .field label widget => [{ widget, labels := [label], indices := [] }]
  | .group label children =>
    (List.finRange _).flatMap fun index =>
      ((children index).fieldRefs value (localValue index)).map fun field =>
        { field with labels := label :: field.labels, indices := index.val :: field.indices }
  | .list label item _ =>
    (localValue.zipIdx).flatMap fun (entry, index) =>
      (item.fieldRefs entry entry).map fun field =>
        { field with
          labels := label :: toString (index + 1) :: field.labels
          indices := index :: field.indices }
  | .visibleWhen condition body =>
    if condition.eval value then body.fieldRefs value localValue else []

end Forms
