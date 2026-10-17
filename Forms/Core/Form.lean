import Forms.Core.Expr

namespace Forms

inductive Widget : (t : DataType) → Type 1 where
  | textInput : Widget .text
  | checkbox : Widget .boolean
  | naturalInput : Widget .natural
  | dateInput : Widget .date
  | select {domain : Enum} : Widget (.enum domain)

inductive Form : (root : DataType) → (t : DataType) → Type 1 where
  | field {root t : DataType}
      (label : String)
      (widget : Widget t)
      : Form root t
  | group {root : DataType} {fields : Enum} {children : fields → DataType}
      (label : String)
      (forms : (i : fields) → Form root (children i))
      : Form root (.record fields children)
  | sum {root : DataType} {tags : Enum} {constructors : tags → DataType}
      (label : String)
      (branches : (i : tags) → Form (constructors i) (constructors i))
      (defaults : (i : tags) → DataType.denote (constructors i))
      : Form root (.sum tags constructors)
  | list {root element : DataType}
      (label : String)
      (item : Form element element)
      (defaultItem : DataType.denote element)
      : Form root (.list element)
  | visibleWhen {root t : DataType}
      (condition : Expr root .boolean)
      (body : Form root t)
      : Form root t

structure FieldRef where
  {t : DataType}
  widget : Widget t
  labels : List String
  indices : List Nat

def Form.fieldRefs {root t : DataType} (form : Form root t)
    (value : DataType.denote root) (localValue : DataType.denote t) : List FieldRef :=
  match form with
  | .field label widget => [{ widget, labels := [label], indices := [] }]
  | .group label children =>
    (FinEnum.toList _).flatMap fun index =>
      (Form.fieldRefs (children index) value (localValue index)).map fun field =>
        { field with labels := label :: field.labels, indices := (FinEnum.equiv index).val :: field.indices }
  | .sum (tags := tags) label branches _ =>
    (Form.fieldRefs (branches localValue.tag) localValue.payload localValue.payload).map fun field =>
      { field with labels := label :: tags.label localValue.tag :: field.labels
                   indices := (FinEnum.equiv localValue.tag).val :: field.indices }
  | .list label item _ =>
    (localValue.zipIdx).flatMap fun (entry, index) =>
      (Form.fieldRefs item entry entry).map fun field =>
        { field with
          labels := label :: toString (index + 1) :: field.labels
          indices := index :: field.indices }
  | .visibleWhen condition body =>
    if Expr.eval condition value then Form.fieldRefs body value localValue else []

end Forms
