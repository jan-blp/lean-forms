module

public import Forms.Model.Sugar

@[expose] public section
namespace Forms.ExampleForms.SharedState
open Forms.Model Forms.Model.Sugar

def consumer
  {Γ : Context}
  (shared : Var Γ Nat)
  : Component Γ Nat := named%[shared]
  state% own := (0 : Nat);
  .group "" [
    .computed "Item" { inputs := inputs[path[]], run := toString },
    .computed "Shared count" { inputs := inputs[.ui ref[shared]], run := toString },
    .computed "Private count" { inputs := inputs[.ui ref[own]], run := toString },
    .button "Increment shared" (.set ref[shared] {
      inputs := inputs[.ui ref[shared]], run := fun count => count + 1 }),
    .button "Increment private" (.set ref[own] {
      inputs := inputs[.ui ref[own]], run := fun count => count + 1 })]

def form : Component [] (List (Item Nat)) := named%
  state% shared := (0 : Nat);
  .group "Shared local state" [
    Component.void <| .list .self "Consumers" (.numbered "Consumer") "Add consumer"
        (Item.mkWithoutUuid 0) (.zoom path[Item.Field.value] (consumer ref[shared])),
    .computed "Shared count outside the list" {
      inputs := inputs[.ui ref[shared]], run := toString },
    .button "Clear shared" (.set ref[shared] (.const 0))]

def initial : List (Item Nat) := IdGen.run ([10, 20].mapM Item.fresh)

end Forms.ExampleForms.SharedState
