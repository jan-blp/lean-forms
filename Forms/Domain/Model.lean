namespace Forms

inductive Ty where
  | text
  | boolean
  | natural
  | pair (left right : Ty)
  deriving Repr, DecidableEq

abbrev Ty.denote (type : Ty) : Type :=
  match type with
  | .text => String
  | .boolean => Bool
  | .natural => Nat
  | .pair left right => Ty.denote left × Ty.denote right

inductive Path : (root : Ty) → (target : Ty) → Type where
  | here {type : Ty} : Path type type
  | left
      {l r target : Ty}
      (rest : Path l target)
      : Path (.pair l r) target
  | right
      {l r target : Ty}
      (rest : Path r target)
      : Path (.pair l r) target

def Path.get
    {root target : Ty}
    (path : Path root target)
    (value : Ty.denote root)
    : Ty.denote target :=
  match path with
  | .here => value
  | .left rest => Path.get rest value.1
  | .right rest => Path.get rest value.2

def Path.set
    {root target : Ty}
    (path : Path root target)
    (replacement : Ty.denote target)
    (value : Ty.denote root)
    : Ty.denote root :=
  match path with
  | .here => replacement
  | .left rest => (Path.set rest replacement value.1, value.2)
  | .right rest => (value.1, Path.set rest replacement value.2)

def Path.trans
    {a b c : Ty}
    (p1 : Path a b)
    (p2 : Path b c)
    : Path a c :=
  match p1 with
  | .here => p2
  | .left rest => .left (Path.trans rest p2)
  | .right rest => .right (Path.trans rest p2)

def Path.Labels {root target : Ty} (path : Path root target) : Type :=
  match path with
  | .here => String
  | .left rest => String × Path.Labels rest
  | .right rest => String × Path.Labels rest

def Path.Labels.toList
    {root target : Ty}
    {path : Path root target}
    (labels : Path.Labels path)
    : List String :=
  match path with
  | .here => [labels]
  | .left rest => labels.1 :: Path.Labels.toList (path := rest) labels.2
  | .right rest => labels.1 :: Path.Labels.toList (path := rest) labels.2

inductive Expr (root : Ty) : (result : Ty) → Type where
  | value {t : Ty} (v : Ty.denote t) : Expr root t
  | project {t : Ty} (p : Path root t) : Expr root t
  | not (e : Expr root .boolean) : Expr root .boolean
  | and (l r : Expr root .boolean) : Expr root .boolean
  | textEquals (l r : Expr root .text) : Expr root .boolean
  | natLe (l r : Expr root .natural) : Expr root .boolean

def Expr.eval
    {root type : Ty}
    (expression : Expr root type)
    (value : Ty.denote root)
    : Ty.denote type :=
  match expression with
  | .value constant => constant
  | .project path => Path.get path value
  | .not operand => !(Expr.eval operand value)
  | .and left right => Expr.eval left value && Expr.eval right value
  | .textEquals left right => Expr.eval left value == Expr.eval right value
  | .natLe left right => decide (Expr.eval left value ≤ Expr.eval right value)

inductive Control : (type : Ty) → Type where
  | text : Control .text
  | checkbox : Control .boolean
  | natural : Control .natural

inductive Form (root : Ty) : (type : Ty) → Type where
  | field
      {t : Ty}
      (label : String)
      (control : Control t)
      : Form root t
  | group
      {l r : Ty}
      (label : String)
      (left : Form root l)
      (right : Form root r)
      : Form root (.pair l r)
  | visibleWhen
      {t : Ty}
      (condition : Expr root .boolean)
      (body : Form root t)
      : Form root t

structure FieldRef (root : Ty) where
  type : Ty
  path : Path root type
  labels : Path.Labels path
  control : Control type

def Form.fieldRefs
    {root type : Ty}
    (form : Form root type)
    (value : Ty.denote root)
    : List (FieldRef type) :=
  match form with
  | .field label control =>
    [{ type := type
       path := .here
       labels := label
       control := control }]
  | @Form.group _ l r label left right =>
    let leftFields : List (FieldRef (.pair l r)) :=
      List.map (fun (field : FieldRef l) =>
        { field with
          path := .left field.path
          labels := (label, field.labels) })
        (Form.fieldRefs left value)
    let rightFields : List (FieldRef (.pair l r)) :=
      List.map (fun (field : FieldRef r) =>
        { field with
          path := .right field.path
          labels := (label, field.labels) })
        (Form.fieldRefs right value)
    leftFields ++ rightFields
  | .visibleWhen condition body =>
    if Expr.eval condition value then Form.fieldRefs body value else []

end Forms
