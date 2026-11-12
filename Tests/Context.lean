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
  fail_if_success have bad : Var [Bool] Nat := .here
  fail_if_success have bad : Var [Nat] Bool := .there .here
  trivial

def run : IO Unit := do
  let first : Var [Nat, Nat] Nat := .here
  let second : Var [Nat, Nat] Nat := .there .here
  let initial : Env [Nat, Nat] := env[10, 20]
  let changed := second.set 30 initial
  check "ContextSeparatesSameTypeVariables" (first.get changed == 10 && second.get changed == 30)
  -- Function-valued state needs no serialization or runtime type information.
  let function : Var [Nat → Nat] (Nat → Nat) := .here
  let functions : Env [Nat → Nat] := env[fun n => n + 1]
  check "ContextStoresValuesWithoutCodecs" (function.get functions 41 == 42)
  let form : Component [] Nat := .bind (7 : Nat) (.bind "filter"
    (.computed "Summary" {
      inputs := inputs[.ui (Var.here : Var [String, Nat] String), .ui (Var.there Var.here)]
      run := fun text count => s!"{text}: {count}"
    }))
  check "FormInitializesLexicalVariables"
    ((ModelView.render form 0 {} [] Env.nil).view == .computed "Summary" "filter: 7")

end Tests.Context
