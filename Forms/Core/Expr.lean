import Forms.Core.Path

namespace Forms

inductive Expr : (input : DataType) → (result : DataType) → Type 1 where
  | value {input result : DataType} (v : ⟦result⟧) : Expr input result
  | project {input t : DataType} (p : Path input t) : Expr input t
  | all {input element : DataType}
      (items : Expr input (.list element))
      (predicate : Expr element .boolean)
      : Expr input .boolean
  | cases {input result : DataType} {tags : Enum} {constructors : tags → DataType}
      (subject : Expr input (.sum tags constructors))
      (branches : (i : tags) → Expr (constructors i) result) : Expr input result
  | sum {input element : DataType}
      (items : Expr input (.list element))
      (value : Expr element .natural) : Expr input .natural
  | filter {input element : DataType}
      (items : Expr input (.list element)) (predicate : Expr element .boolean)
      : Expr input (.list element)
  | sortBy {input element : DataType}
      (items : Expr input (.list element)) (key : Expr element .text) (descending : Bool)
      : Expr input (.list element)
  | search {input element : DataType}
      (items : Expr input (.list element)) (key : Expr element .text)
      (query : Expr input .text) : Expr input (.list element)
  | sortNatBy {input element : DataType}
      (items : Expr input (.list element)) (key : Expr element .natural) (descending : Bool)
      : Expr input (.list element)
  | length {input element : DataType} (items : Expr input (.list element)) : Expr input .natural
  | enumCases {input result : DataType} {domain : Enum}
      (subject : Expr input (.enum domain)) (branches : domain → Expr input result) : Expr input result
  | enumEq {input : DataType} {domain : Enum}
      (left right : Expr input (.enum domain)) : Expr input .boolean
  | enumLabel {input : DataType} {domain : Enum} (subject : Expr input (.enum domain)) : Expr input .text
  | ifThenElse {input result : DataType} (condition : Expr input .boolean)
      (whenTrue whenFalse : Expr input result) : Expr input result
  | natToText {input : DataType} (value : Expr input .natural) : Expr input .text
  | textAppend {input : DataType} (left right : Expr input .text) : Expr input .text
  | natAdd {input : DataType}
    (l r : Expr input .natural)
    : Expr input .natural
  | natSub {input : DataType}
    (l r : Expr input .natural)
    : Expr input .natural
  | natMul {input : DataType} (l r : Expr input .natural) : Expr input .natural
  | not {input : DataType} (operand : Expr input .boolean) : Expr input .boolean
  | and {input : DataType} (l r : Expr input .boolean) : Expr input .boolean
  | dateLe {input : DataType} (l r : Expr input .date) : Expr input .boolean
  | natLe {input : DataType} (l r : Expr input .natural) : Expr input .boolean

def Expr.eval {input t : DataType}
  (expression : Expr input t)
  (value : ⟦input⟧)
  : ⟦t⟧ :=
  match expression with
  | .value constant => constant
  | .project path => Path.get path value
  | .all items predicate => List.all (Expr.eval items value) (Expr.eval predicate)
  | .cases subject branches =>
    let selected := Expr.eval subject value
    Expr.eval (branches selected.tag) selected.payload
  | .sum items expression => List.sum ((Expr.eval items value).map (Expr.eval expression))
  | .filter items predicate => (Expr.eval items value).filter (Expr.eval predicate)
  | .sortBy items key descending =>
    (Expr.eval items value).mergeSort fun left right =>
      if descending then Expr.eval key right ≤ Expr.eval key left
      else Expr.eval key left ≤ Expr.eval key right
  | .search items key query =>
    (Expr.eval items value).filter fun row =>
      (Expr.eval key row).toLower.contains (Expr.eval query value).toLower
  | .sortNatBy items key descending =>
    (Expr.eval items value).mergeSort fun left right =>
      if descending then Expr.eval key right ≤ Expr.eval key left
      else Expr.eval key left ≤ Expr.eval key right
  | .length items => (Expr.eval items value).length
  | .enumCases subject branches => Expr.eval (branches (Expr.eval subject value)) value
  | .enumEq left right => decide (Expr.eval left value = Expr.eval right value)
  | .enumLabel (domain := domain) subject => domain.label (Expr.eval subject value)
  | .ifThenElse condition whenTrue whenFalse =>
    if Expr.eval condition value then Expr.eval whenTrue value else Expr.eval whenFalse value
  | .natToText operand => toString (Expr.eval operand value)
  | .textAppend left right => Expr.eval left value ++ Expr.eval right value
  | .natAdd left right => Expr.eval left value + Expr.eval right value
  | .natSub left right => Expr.eval left value - Expr.eval right value
  | .natMul left right => Expr.eval left value * Expr.eval right value
  | .not operand => !Expr.eval operand value
  | .and left right => Expr.eval left value && Expr.eval right value
  | .dateLe left right => Expr.eval left value ≤ Expr.eval right value
  | .natLe left right => Expr.eval left value ≤ Expr.eval right value

section

variable {outer input result : DataType}

def Expr.weaken {outer input result}
  (path : Path outer input)
  (expression : Expr input result)
  : Expr outer result :=
  match expression with
  | .value v => .value v
  | .project field => .project (Path.trans path field)
  | .all items predicate => .all (Expr.weaken path items) predicate
  | .cases subject branches => .cases (Expr.weaken path subject) branches
  | .sum items expression => .sum (Expr.weaken path items) expression
  | .filter items predicate => .filter (Expr.weaken path items) predicate
  | .sortBy items key descending => .sortBy (Expr.weaken path items) key descending
  | .search items key query => .search (Expr.weaken path items) key (Expr.weaken path query)
  | .sortNatBy items key descending => .sortNatBy (Expr.weaken path items) key descending
  | .length items => .length (Expr.weaken path items)
  | .enumCases subject branches =>
    .enumCases (Expr.weaken path subject) (fun choice => Expr.weaken path (branches choice))
  | .enumEq left right => .enumEq (Expr.weaken path left) (Expr.weaken path right)
  | .enumLabel subject => .enumLabel (Expr.weaken path subject)
  | .ifThenElse condition whenTrue whenFalse =>
    .ifThenElse (Expr.weaken path condition) (Expr.weaken path whenTrue) (Expr.weaken path whenFalse)
  | .natToText operand => .natToText (Expr.weaken path operand)
  | .textAppend left right => .textAppend (Expr.weaken path left) (Expr.weaken path right)
  | .natAdd l r => .natAdd (Expr.weaken path l) (Expr.weaken path r)
  | .natSub l r => .natSub (Expr.weaken path l) (Expr.weaken path r)
  | .natMul l r => .natMul (Expr.weaken path l) (Expr.weaken path r)
  | .not operand => .not (Expr.weaken path operand)
  | .and l r => .and (Expr.weaken path l) (Expr.weaken path r)
  | .dateLe l r => .dateLe (Expr.weaken path l) (Expr.weaken path r)
  | .natLe l r => .natLe (Expr.weaken path l) (Expr.weaken path r)

end

end Forms
