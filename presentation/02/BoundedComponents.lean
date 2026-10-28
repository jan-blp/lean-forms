import Forms.Core.Component.Builder

namespace Forms.Composition

def Component.fieldCount {state : DataType}
    (component : Component state) : Nat :=
  match component with
  | .field .. => 1
  | .stack (items := items) _ children _ =>
      ((FinEnum.toList items).map (fun i => (children i).fieldCount)).sum
  | .list _ _ item _ => item.fieldCount
  | .sum (tags := tags) _ _ branches _ =>
      ((FinEnum.toList tags).map (fun tag => (branches tag).fieldCount)).sum
  | .computed .. => 1
  | .visibleWhen _ body => body.fieldCount
  | .disabledWhen _ body => body.fieldCount

structure BoundedComponent (N : Nat) (state : DataType) where
  component : Component state
  bounded : component.fieldCount ≤ N := by decide

namespace BoundedExample

inductive ProfileField where
  | name
  | email
  -- | age
  deriving DecidableEq

instance : FinEnum ProfileField :=
  -- FinEnum.ofList [.name, .email, .age] (by grind [ProfileField])
  FinEnum.ofList [.name, .email] (by grind [ProfileField])

def profileFields : Enum where
  type := ProfileField
  label
    | .name => "name"
    | .email => "email"
    -- | .age => "age"

abbrev profile : DataType := .record profileFields fun
  | .name => .text
  | .email => .text
  -- | .age => .natural

open Component in
def profileForm : BoundedComponent 2 profile where
  component :=
    Builder.group (fields := profileFields) "Profile" (children := fun
      | .name => Builder.field "Name" .textInput
      | .email => Builder.field "Email" .textInput)
    |>.build

end BoundedExample

end Forms.Composition
