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

def indexedRef (ref : Array Nat) : Nat := (ref)[0]!

def indexedSlot (slot : Array Nat) : Nat := (slot)[0]!

example : indexedRef #[7] = 7 := by decide
example : indexedSlot #[8] = 8 := by decide

def namedCounter : Component [] Nat Nat := named%
  state% count := (1 : Nat);
  .output { inputs := inputs[.ui ref[count]], run := id }

example : namedCounter = .bind (1 : Nat) (.output { inputs := inputs[.ui .here], run := id }) := rfl

def refInputs : Component [] Nat Nat := named%
  state% count := (1 : Nat);
  state% _ := false;
  .output { inputs := inputs[ref[count], path[]], run := Nat.add }

example :
    refInputs =
    .bind (1 : Nat) (.bind false (.output {
      inputs := inputs[.ui (.there .here), path[]]
      run := Nat.add })) := rfl

def refComputeInputs : Component [] Nat Nat := named%
  state% count := (1 : Nat);
  state% step := (2 : Nat);
  .output
    (compute%
      (count : Nat) ← ref[count],
      step ← ref[step],
      value ← path[]
      => count + step + value)

example :
    refComputeInputs =
    .bind (1 : Nat) (.bind (2 : Nat) (.output {
      inputs := inputs[.ui (.there .here), .ui .here, path[]]
      run := fun count step value => count + step + value })) := rfl

def named_tab_labels : Nat := 5

example : named_tab_labels% 2 = 1 := by decide

end

def lastRef (ref : Array Nat) : Nat := ref[ref.size - 1]!

def lastSlot (slot : Array Nat) : Nat := slot[slot.size - 1]!

example : lastRef #[1, 2] = 2 := by decide
example : lastSlot #[3, 4] = 4 := by decide

end Tests.Sugar.Parsing
