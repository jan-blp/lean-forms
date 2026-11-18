module

public import Forms.ExampleForms.Person
public import Forms.Runtime.ServerForm
public import Forms.ExampleForms.Receipts.Server
public import Tests.FreshId

public section
namespace Tests.ServerForm
open Lean Forms.Runtime Forms.ExampleForms Forms.Model

private def check (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"

private def alreadySubmitted (raw : Receipts.Raw) : List Bool :=
  raw.receipts.map (·.alreadySubmitted.value)

private def repeated : Receipts.Raw :=
  ⟨[⟨firstId, "R-1", ⟨false⟩⟩, ⟨secondId, "R-2", ⟨false⟩⟩, ⟨thirdId, "R-1", ⟨false⟩⟩]⟩

example : (ModelForm.validationErrors (model := Receipts) repeated).map (·.targets) = [
    .locations [.field "receipts", .item firstId, .field "number"]
      [[.field "receipts", .item thirdId, .field "number"]]] := by
  decide

private def submission (fingerprint : String) (value : Person.Raw) : Json :=
  toJson ({ form := "person", fingerprint, value } : Submission Person.Raw)

def run : IO Unit := do
  let server : ServerForm := {
    form := { definition := .ofModel Person Person.form Person.initial, submitUrl := "/api/submit" }
    State := IO.Ref Nat
    init := IO.mkRef 0
    store := fun stores (value : Person.Raw) => do
      stores.modify (· + 1)
      pure { value with name := "Stored" } }
  let stores : IO.Ref Nat ← server.init
  let submit fingerprint value :=
    (server.submit stores "person" "current" (submission fingerprint value)).run
  let stale ← submit "old" Person.initial
  let invalid ← submit "current" { Person.initial with name := "" }
  check "RejectedSubmissionsAreNotStored"
    (stale matches .error (.invalidRequest _) && invalid matches .error (.validation ..) &&
      (← stores.get) == 0)
  let stored ← submit "current" Person.initial
  check "SubmitAnswersWithTheStoredDocument"
    ((stored.toOption.bind fun saved => (saved.getObjValAs? Person.Raw "value").toOption).map
      (·.name) == some "Stored" && (← stores.get) == 1)

  let state ← Receipts.ServerState.init
  let first : Receipt.Raw := ⟨firstId, "R-1", ⟨false⟩⟩
  let copy := { first with id := secondId }
  let submitted ← Receipts.serverCheck state ⟨[first]⟩
  let resubmitted ← Receipts.serverCheck state ⟨[first]⟩
  let replaced ← Receipts.serverCheck state ⟨[copy]⟩
  check "OnlyNumbersClaimedOutsideTheSubmissionWereAlreadySubmitted"
    (alreadySubmitted submitted == [false] && alreadySubmitted resubmitted == [false] &&
      alreadySubmitted replaced == [true])

end Tests.ServerForm
