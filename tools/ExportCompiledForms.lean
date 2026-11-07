module

import Forms.Runtime.CompiledForms
meta import Forms.Runtime.CompiledForms

open Forms Forms.Runtime Forms.ExampleForms

public def main : IO Unit := do
  IO.println (Lean.toJson ((FinEnum.toList Example).map fun selected =>
    Lean.Json.mkObj [("descriptor", CompiledForms.descriptor selected),
      ("specification", CompositionProtocol.specificationToJson selected.definition.refined
        selected.definition.component selected.definition.initial)])).compress
