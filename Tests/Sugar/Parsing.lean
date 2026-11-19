module

public import Forms

@[expose] public section
namespace Tests.Sugar.Parsing
open Forms.Model

def firstRef (ref : Array Nat) : Nat := ref[0]!

def firstSlot (slot : Array Nat) : Nat := slot[0]!

example : firstRef #[7] = 7 := by decide
example : firstSlot #[8] = 8 := by decide

section
open Forms.Model.Sugar

def namedCounter : Component [] Nat Nat := named%
  state% count := (1 : Nat);
  .output { inputs := inputs[.ui ref[count]], run := id }

example : namedCounter = .bind (1 : Nat) (.output { inputs := inputs[.ui .here], run := id }) := rfl

def named_tab_labels : Nat := 5

example : named_tab_labels% 2 = 1 := by decide

end

def lastRef (ref : Array Nat) : Nat := ref[ref.size - 1]!

def lastSlot (slot : Array Nat) : Nat := slot[slot.size - 1]!

example : lastRef #[1, 2] = 2 := by decide
example : lastSlot #[3, 4] = 4 := by decide

end Tests.Sugar.Parsing
