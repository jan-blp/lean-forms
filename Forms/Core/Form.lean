import Forms.Core.Expr

namespace Forms

inductive Widget : (t : DataType) → Type 1 where
  | textInput : Widget .text
  | checkbox : Widget .boolean
  | naturalInput : Widget .natural
  | select {domain : Choice} : Widget (.choice domain)

inductive Form (root : DataType) : (t : DataType) → Type 1 where
  | field
      {t : DataType}
      (label : String)
      (widget : Widget t)
      : Form root t
  | group
      {n : Nat} {children : Fin n → DataType}
      (label : String)
      (fields : (i : Fin n) → Form root (children i))
      : Form root (.group children)
  | visibleWhen
      {t : DataType}
      (condition : Expr root .boolean)
      (body : Form root t)
      : Form root t

structure FieldRef (root : DataType) where
  type : DataType
  path : Path root type
  labels : Path.Labels path
  widget : Widget type

def Form.fieldRefs
    {root t : DataType}
    (form : Form root t)
    (value : DataType.denote root)
    : List (FieldRef t) :=
  match form with
  | .field label widget =>
    [{ type := t
       path := .here
       labels := label
       widget := widget }]
  | .group label children =>
    (List.finRange _).flatMap fun index =>
      (Form.fieldRefs (children index) value).map fun field =>
        { field with
          path := .child index field.path
          labels := (label, field.labels) }
  | .visibleWhen condition body =>
    if Expr.eval condition value then Form.fieldRefs body value else []

end Forms
