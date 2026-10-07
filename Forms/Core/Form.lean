import Forms.Core.Expr

namespace Forms

inductive Widget : (type : DataType) → Type where
  | textInput : Widget .text
  | checkbox : Widget .boolean
  | naturalInput : Widget .natural

inductive Form (root : DataType) : (type : DataType) → Type where
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
    {root type : DataType}
    (form : Form root type)
    (value : DataType.denote root)
    : List (FieldRef type) :=
  match form with
  | .field label widget =>
    [{ type := type
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
