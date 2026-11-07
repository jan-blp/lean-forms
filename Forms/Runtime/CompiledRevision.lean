module

public import Forms.ExampleForms.Example
public import Forms.Runtime.CompiledView
meta import Lean.Elab.Term

open Lean Elab Term in
/-- Hash compiled declarations during elaboration; no definition encoder is linked into Wasm. -/
elab "compiled_revision%" : term => do
  let env ← getEnv
  let declarations := env.constants.toList.filter fun (name, _) =>
    (name.toString.splitOn "Forms.").length > 1
  let declarations := declarations.mergeSort fun a b => a.1.toString ≤ b.1.toString
  let digest := declarations.foldl (fun (h : UInt64) (name, info) =>
    mixHash h (hash (name, info.type, info.value? (allowOpaque := true)))) 0
  return mkStrLit ("compiled-2-" ++ toString digest)

public def Forms.Runtime.compiledRevision : String := compiled_revision%
