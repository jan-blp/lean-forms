module

public import Forms.Runtime.CompiledForms
public import Tests.ServerRefinements

@[expose] public section

namespace Tests.CompiledForms
open Lean Forms Forms.Runtime Forms.ExampleForms Forms.Composition

def check (message : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError message)

def request (operation handle : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj ([("operation", toJson operation), ("handle", toJson handle)] ++ fields)

def openRequest (selected : Example) : Json :=
  Json.mkObj [("operation", toJson "open"), ("form", toJson selected.name),
    ("revision", toJson (compiledRevision)),
    ("value", JsonProtocol.valueToJson selected.definition.initial)]

def run : IO Unit := do
  let (store, opened) ← IO.ofExcept (CompiledForms.execute {} (openRequest .counter))
  let handle ← IO.ofExcept (opened.getObjValAs? String "handle")
  let key := (toJson [toJson ([] : List Json), toJson "plusOne"]).compress
  let action := request "apply" handle [("key", toJson key)]
  let (updated, snapshot) ← IO.ofExcept (CompiledForms.execute store action)
  let submission ← IO.ofExcept (snapshot.getObjVal? "submission")
  discard <| IO.ofExcept ((ComponentHistoryProtocol.verify Counter.form 0 submission).mapError toString)
  check "Compiled action changes value" ((← IO.ofExcept (submission.getObjValAs? String "value")) == "1")
  let (_, reset) ← IO.ofExcept (CompiledForms.execute updated (request "reset" handle))
  check "Compiled reset restores initial value"
    ((← IO.ofExcept ((← IO.ofExcept (reset.getObjVal? "submission")).getObjValAs? String "value")) == "0")
  let (disposed, _) ← IO.ofExcept (CompiledForms.execute updated (request "dispose" handle))
  check "Disposed handles reject actions" ((CompiledForms.execute disposed action).isOk == false)
  let (reopened, next) ← IO.ofExcept (CompiledForms.execute disposed (openRequest .counter))
  check "Handles are not reused" ((← IO.ofExcept (next.getObjValAs? String "handle")) != handle)
  check "Old handles stay invalid" ((CompiledForms.execute reopened action).isOk == false)
  check "Failed actions are rejected" ((CompiledForms.execute updated
    (request "apply" handle [("key", toJson "missing")])).isOk == false)
  check "Unknown operations are rejected" ((CompiledForms.execute updated (request "unknown" handle)).isOk == false)
  check "Server-only checks stay on server" ((CompiledForms.clientErrors (Tests.ServerRefinements.even) 3).isEmpty)
  check "Client checks still run inside server refinements"
    (!(CompiledForms.clientErrors (Tests.ServerRefinements.even Tests.ServerRefinements.positive) 0).isEmpty)
  for selected in FinEnum.toList Example do
    let (_, result) ← IO.ofExcept (CompiledForms.execute {} (openRequest selected))
    check "Compiled initialization returns a snapshot" ((result.getObjVal? "snapshot").isOk)
  let guarded := Component.disabledWhen (.value true) Counter.form
  let blocked := CompiledView.render guarded 0
  check "Disabled controls are rendered disabled" (blocked.controls.all (·.disabled))
  check "Disabled controls cannot be invoked" ((CompiledView.invocation guarded 0 key none).isOk == false)
  let hidden := Component.visibleWhen (.value false) Counter.form
  check "Hidden controls are omitted" ((CompiledView.render hidden 0).controls.isEmpty)
  check "Hidden controls cannot be invoked" ((CompiledView.invocation hidden 0 key none).isOk == false)
  IO.println "PASS: compiled model actions, replay, reset, disposal, guards, and server-only validation"

end Tests.CompiledForms
