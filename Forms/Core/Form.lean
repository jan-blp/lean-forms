import Forms.Core.Expr

namespace Forms

inductive Widget : (type : DataType) → Type where
  | textInput : Widget .text
  | checkbox : Widget .boolean
  | naturalInput : Widget .natural

inductive Form : (type : DataType) → Type where
  | field
      {t : DataType}
      (label : String)
      (widget : Widget t)
      : Form t

structure FieldRef (root : DataType) where
  type : DataType
  path : Path root type
  labels : Path.Labels path
  widget : Widget type

def Form.fieldRefs
    {type : DataType}
    (form : Form type)
    : List (FieldRef type) :=
  match form with
  | .field label widget =>
    [{ type := type
       path := .self
       labels := label
       widget := widget }]

end Forms
