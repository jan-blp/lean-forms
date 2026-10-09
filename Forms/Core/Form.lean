import Forms.Core.Expr

namespace Forms

inductive Widget : (type : DataType) → Type 1 where
  | textInput : Widget .text
  | checkbox : Widget .boolean
  | naturalInput : Widget .natural
  | dateInput : Widget .date
  | select {domain : Enum} : Widget (.enum domain)

inductive Form : (type : DataType) → Type 1 where
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
