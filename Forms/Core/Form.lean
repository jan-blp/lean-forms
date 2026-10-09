import Forms.Core.Expr

namespace Forms

inductive Control : (type : DataType) → Type 1 where
  | text : Control .text
  | checkbox : Control .boolean
  | natural : Control .natural
  | choice {domain : Choice} : Control (.choice domain)

inductive Form (root : DataType) : (type : DataType) → Type 1 where
  | field
      {t : DataType}
      (label : String)
      (control : Control t)
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
  control : Control type

def Form.fieldRefs
    {root type : DataType}
    (form : Form root type)
    (value : DataType.denote root)
    : List (FieldRef type) :=
  match form with
  | .field label control =>
    [{ type := type
       path := .here
       labels := label
       control := control }]
  | .group label children =>
    (List.finRange _).flatMap fun index =>
      (Form.fieldRefs (children index) value).map fun field =>
        { field with
          path := .child index field.path
          labels := (label, field.labels) }
  | .visibleWhen condition body =>
    if Expr.eval condition value then Form.fieldRefs body value else []

end Forms
