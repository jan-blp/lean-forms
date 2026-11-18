module

public import Forms.ExampleForms.Person
public import Forms.Runtime.ServerForm

public section
namespace Tests.ServerForm
open Lean Forms.Runtime Forms.ExampleForms

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

private def submission (fingerprint : String) (value : Person.Raw) : Json :=
  toJson ({ form := "person", fingerprint, value } : Submission Person.Raw)

def run : IO Unit := do
  let stores ← IO.mkRef 0
  let server : ServerForm := {
    form := { definition := .ofModel Person Person.form Person.initial, submitUrl := "/api/submit" }
    store := fun (value : Person.Raw) => do
      stores.modify (· + 1)
      pure { value with name := "Stored" } }
  let submit fingerprint value :=
    (server.submit "person" "current" (submission fingerprint value)).run
  let stale ← submit "old" Person.initial
  let invalid ← submit "current" { Person.initial with name := "" }
  check "RejectedSubmissionsAreNotStored"
    (stale matches .error (.invalidRequest _) && invalid matches .error (.validation ..) &&
      (← stores.get) == 0)
  let stored ← submit "current" Person.initial
  check "SubmitAnswersWithTheStoredDocument"
    ((stored.toOption.bind fun saved => (saved.getObjValAs? Person.Raw "value").toOption).map
      (·.name) == some "Stored" && (← stores.get) == 1)

end Tests.ServerForm
