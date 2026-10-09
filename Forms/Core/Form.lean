import Forms.Core.Expr

namespace Forms

inductive Widget : (type : DataType) → Type 1 where
  | textInput : Widget .text
  | checkbox : Widget .boolean
  | naturalInput : Widget .natural
  | dateInput : Widget .date
  | select {domain : Enum} : Widget (.enum domain)

inductive Form (root : DataType) : (type : DataType) → Type 1 where
  | field
      {t : DataType}
      (label : String)
      (widget : Widget t)
      : Form root t

structure FieldRef (root : DataType) where
  type : DataType
  path : Path root type
  labels : Path.Labels path
  widget : Widget type

def Form.fieldRefs
    {root type : DataType}
    (form : Form root type)
    (_value : DataType.denote root)
    : List (FieldRef type) :=
  match form with
  | .field label widget =>
    [{ type := type
       path := .self
       labels := label
       widget := widget }]

end Forms
