module

public import Forms.Model.Component
meta import Forms.Model.Context.Theorems
public import Forms.Runtime.ModelView

public section
namespace Tests.Context
open Forms.Model Forms.Runtime

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

-- Neither a missing variable nor a reference at the wrong type can be constructed.
example : True := by
  fail_if_success have bad : Var [] Nat := .here
  fail_if_success have bad : Var [⟨.writable, Bool⟩] Nat := .here
  fail_if_success have bad : Var [⟨.writable, Nat⟩] Bool := .there .here
  trivial

-- Read-only inputs cannot be used as writable variables, even at the same value type.
example : True := by
  let input : InputRef [⟨.readOnly, Nat⟩] Nat := .here
  fail_if_success have bad : Var [⟨.readOnly, Nat⟩] Nat := .here
  fail_if_success have bad : Var [⟨.writable, Bool⟩, ⟨.readOnly, Nat⟩] Nat := .there .here
  fail_if_success have bad := input.set 42 env[7]
  trivial

-- A table's selection must refer to writable state.
example : True := by
  let input : InputRef [⟨.readOnly, RowSelection⟩] RowSelection := .here
  fail_if_success
    have bad : Component [⟨.readOnly, RowSelection⟩] (List Nat) :=
      .table .self "Numbers" "Number" 0 columns[] (some input)
  trivial

def run : IO Unit := do
  let first : Var [⟨.writable, Nat⟩, ⟨.writable, Nat⟩] Nat := .here
  let second : Var [⟨.writable, Nat⟩, ⟨.writable, Nat⟩] Nat := .there .here
  let initial : Env [⟨.writable, Nat⟩, ⟨.writable, Nat⟩] := env[10, 20]
  let changed := second.set 30 initial
  check "ContextSeparatesSameTypeVariables" (first.get changed == 10 && second.get changed == 30)
  -- Function-valued state needs no serialization or runtime type information.
  let function : Var [⟨.writable, Nat → Nat⟩] (Nat → Nat) := .here
  let functions : Env [⟨.writable, Nat → Nat⟩] := env[fun n => n + 1]
  check "ContextStoresValuesWithoutCodecs" (function.get functions 41 == 42)
  let form : Component [] Nat := .bind (7 : Nat) (.bind "filter"
    (.computed "Summary" {
      inputs := inputs[.ui (Ref.here : Var [⟨.writable, String⟩, ⟨.writable, Nat⟩] String), .ui (Ref.there Ref.here)]
      run := fun text count => s!"{text}: {count}"
    }))
  check "FormInitializesLexicalVariables"
    ((ModelView.render form 0 {} [] Env.nil).view == .computed "Summary" "filter: 7")
  let input : InputRef [⟨.readOnly, String⟩, ⟨.writable, Nat⟩] String := .here
  let count : Var [⟨.readOnly, String⟩, ⟨.writable, Nat⟩] Nat := .there .here
  let mixed : Env [⟨.readOnly, String⟩, ⟨.writable, Nat⟩] := env["Tasks", 2]
  let summary : Computation [⟨.readOnly, String⟩, ⟨.writable, Nat⟩] Nat String := {
    inputs := inputs[.ui input, .ui count, path[]]
    run := fun label count total => s!"{label}: {count}/{total}"
  }
  check "ContextComputationsReadInputsAndState"
    (summary.eval 10 mixed == "Tasks: 2/10" &&
      summary.eval 10 (count.set 3 mixed) == "Tasks: 3/10" &&
      input.get (count.set 3 mixed) == "Tasks")
  let bound : Component [⟨.readOnly, String⟩] Nat := .bind (7 : Nat)
    (.computed "Summary" {
      inputs := inputs[.ui (Ref.there Ref.here), .ui (Ref.here)]
      run := fun label count => s!"{label}: {count}"
    })
  check "ContextBindExtendsReadOnlyContext"
    ((ModelView.render bound 0 {} [] env["Tasks"]).view == .computed "Summary" "Tasks: 7")

end Tests.Context
