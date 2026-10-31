import Forms.ExampleForms.Counter

namespace Forms.ExampleForms.Counters
open Composition

inductive Side where
  | left
  | right
  deriving DecidableEq

instance : FinEnum Side := FinEnum.ofList [.left, .right] (by grind [Side])

def sides : Enum where
  type := Side
  label
    | .left => "left"
    | .right => "right"

def state : DataType := .record sides fun _ => .natural

def initial : ⟦state⟧
  | .left => 0
  | .right => 10

def widget (side : Side) : Component state :=
  .actionWidget (ids := Counter.actionIds) (.field side .self) (sides.label side) Counter.actions

def form : Component state := .stack (items := sides) (some "Counters") widget

end Forms.ExampleForms.Counters
