import Forms.Core.Expr

namespace Forms

inductive Widget : (type : DataType) → Type 1 where
  | textInput : Widget .text
  | checkbox : Widget .boolean
  | naturalInput : Widget .natural

inductive Form (root : DataType) : (type : DataType) → Type 1 where
  | field
      {t : DataType}
      (label : String)
      (widget : Widget t)
      : Form root t
  | group
      {fields : Enum} {children : fields.type → DataType}
      (label : String)
      (forms : (i : fields.type) → Form root (children i))
      : Form root (.record fields children)

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
       path := .self
       labels := label
       widget := widget }]
  | .group label children =>
    (FinEnum.toList _).flatMap fun index =>
      (Form.fieldRefs (children index) value).map fun field =>
        { field with
          path := .child index field.path
          labels := (label, field.labels) }

end Forms
