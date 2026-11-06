module

public import Forms.Runtime.ExpressionProtocol.Schema

@[expose] public section

namespace Forms.Runtime.ExpressionProtocol

def iterationSchema (outer element : Schema) : Schema :=
  .record ["outer", "item", "index"] (by decide) fun i =>
    match i.val with | 0 => outer | 1 => element | _ => .natural

def iterationValue {outer element : Schema}
    (context : ⟦outer.dataType⟧) (item : ⟦element.dataType⟧) (index : Nat) :
    ⟦(iterationSchema outer element).dataType⟧ :=
  fun i => match i with | ⟨0, _⟩ => context | ⟨1, _⟩ => item | ⟨_ + 2, _⟩ => index

/-- A type-checked executable expression. Wire binders need not use the EDSL's label types. -/
structure Program (input result : DataType) : Type 1 where
  eval : ⟦input⟧ → ⟦result⟧

namespace Program

def value {input result : DataType} (v : ⟦result⟧) : Program input result :=
  ⟨fun _ => v⟩

def project {input t : DataType} (p : Path input t) : Program input t :=
  ⟨fun argument => Path.get p argument⟩

def cases {input result : DataType} {tags : Enum} {constructors : tags → DataType}
      (subject : Program input (.sum tags constructors))
      (branches : (i : tags) → Program (constructors i) result) : Program input result :=
  ⟨fun argument => let selected := Program.eval subject argument
    Program.eval (branches selected.tag) selected.payload⟩

def sum {input element : DataType}
      (items : Program input (.list element))
      (value : Program element .natural) : Program input .natural :=
  ⟨fun argument => List.sum ((Program.eval items argument).map (Program.eval value))⟩

def filter {input element : DataType}
      (items : Program input (.list element)) (predicate : Program element .boolean)
      : Program input (.list element) :=
  ⟨fun argument => (Program.eval items argument).filter (Program.eval predicate)⟩

def sortBy {input element : DataType}
      (items : Program input (.list element)) (key : Program element .text) (descending : Bool)
      : Program input (.list element) :=
  ⟨fun argument => (Program.eval items argument).mergeSort fun left right =>
      if descending then Program.eval key right ≤ Program.eval key left
      else Program.eval key left ≤ Program.eval key right⟩

def search {input element : DataType}
      (items : Program input (.list element)) (key : Program element .text)
      (query : Program input .text) : Program input (.list element) :=
  ⟨fun argument => (Program.eval items argument).filter fun row =>
      (Program.eval key row).toLower.contains (Program.eval query argument).toLower⟩

def sortNatBy {input element : DataType}
      (items : Program input (.list element)) (key : Program element .natural) (descending : Bool)
      : Program input (.list element) :=
  ⟨fun argument => (Program.eval items argument).mergeSort fun left right =>
      if descending then Program.eval key right ≤ Program.eval key left
      else Program.eval key left ≤ Program.eval key right⟩

def snoc {input element : DataType}
    (items : Program input (.list element))
    (value : Program input element)
    : Program input (.list element) :=
  ⟨fun argument => Program.eval items argument ++ [Program.eval value argument]⟩

def length {input element : DataType} (items : Program input (.list element)) : Program input .natural :=
  ⟨fun argument => (Program.eval items argument).length⟩

def enumCases {input result : DataType} {domain : Enum}
      (subject : Program input (.enum domain)) (branches : domain → Program input result) : Program input result :=
  ⟨fun argument => Program.eval (branches (Program.eval subject argument)) argument⟩

def enumEq {input : DataType} {domain : Enum}
      (left right : Program input (.enum domain)) : Program input .boolean :=
  ⟨fun argument => decide (Program.eval left argument = Program.eval right argument)⟩

def enumLabel {input : DataType} {domain : Enum} (subject : Program input (.enum domain)) : Program input .text :=
  ⟨fun argument => domain.label (Program.eval subject argument)⟩

def ifThenElse {input result : DataType} (condition : Program input .boolean)
      (whenTrue whenFalse : Program input result) : Program input result :=
  ⟨fun argument => if Program.eval condition argument then Program.eval whenTrue argument else Program.eval whenFalse argument⟩

def natToText {input : DataType} (value : Program input .natural) : Program input .text :=
  ⟨fun argument => toString (Program.eval value argument)⟩

def textEq {input : DataType} (left right : Program input .text) : Program input .boolean :=
  ⟨fun argument => Program.eval left argument == Program.eval right argument⟩

def textAppend {input : DataType} (left right : Program input .text) : Program input .text :=
  ⟨fun argument => Program.eval left argument ++ Program.eval right argument⟩

def natAdd {input : DataType}
    (l r : Program input .natural)
    : Program input .natural :=
  ⟨fun argument => Program.eval l argument + Program.eval r argument⟩

def natSub {input : DataType}
    (l r : Program input .natural)
    : Program input .natural :=
  ⟨fun argument => Program.eval l argument - Program.eval r argument⟩

def natMul {input : DataType} (l r : Program input .natural) : Program input .natural :=
  ⟨fun argument => Program.eval l argument * Program.eval r argument⟩

def not {input : DataType} (operand : Program input .boolean) : Program input .boolean :=
  ⟨fun argument => !Program.eval operand argument⟩

def and {input : DataType} (l r : Program input .boolean) : Program input .boolean :=
  ⟨fun argument => Program.eval l argument && Program.eval r argument⟩

def dateLe {input : DataType} (l r : Program input .date) : Program input .boolean :=
  ⟨fun argument => Program.eval l argument ≤ Program.eval r argument⟩

def natLe {input : DataType} (l r : Program input .natural) : Program input .boolean :=
  ⟨fun argument => Program.eval l argument ≤ Program.eval r argument⟩

def all {input : DataType} {outer element : Schema}
    (items : Program input (.list element.dataType))
    (predicate : Program (iterationSchema outer element).dataType .boolean)
    (context : Path input outer.dataType) : Program input .boolean :=
  ⟨fun value => (items.eval value).zipIdx.all fun (item, index) =>
    predicate.eval (iterationValue (context.get value) item index)⟩

end Program
end Forms.Runtime.ExpressionProtocol
