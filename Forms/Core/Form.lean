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
      (displayOrder : Equiv.Perm fields := Equiv.refl _)
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
  | computed {root t result : DataType}
      (label : String)
      (expression : Expr root result)
      (body : Form root t)
      : Form root t
  | visibleWhen {root t : DataType}
      (condition : Expr root .boolean)
      (body : Form root t)
      : Form root t
  | disabledWhen {root t : DataType}
      (condition : Expr root .boolean)
      (body : Form root t)
      : Form root t

inductive FieldContent (t : DataType) where
  | input (widget : Widget t)
  | computed (value : DataType.denote t)

structure FieldRef where
  {t : DataType}
  content : FieldContent t
  labels : List String
  indices : List Nat
  disabled : Bool := false

def Form.fieldRefs {root t : DataType} (form : Form root t)
    (value : DataType.denote root) (localValue : DataType.denote t) : List FieldRef :=
  match form with
  | .field label widget => [{ content := .input widget, labels := [label], indices := [] }]
  | .group label children displayOrder =>
    (FinEnum.toList _).flatMap fun i =>
      let index := displayOrder i
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
  | .computed label expression body =>
    Form.fieldRefs body value localValue ++
      [{ content := .computed (Expr.eval expression value), labels := [label], indices := [] }]
  | .visibleWhen condition body =>
    if Expr.eval condition value then Form.fieldRefs body value localValue else []

  | .disabledWhen condition body =>
    (Form.fieldRefs body value localValue).map fun field =>
      { field with disabled := field.disabled || Expr.eval condition value }

end Forms
