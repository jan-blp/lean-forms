module

public import Forms.ExampleForms.Registry
public import Forms.Runtime.InputProtocol
public import Tests.FreshId

public section
namespace Tests.Evidence
open Lean Forms.Model Forms.Runtime Forms.ExampleForms

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"FAIL {message}")
  IO.println s!"PASS {message}"

private def perform
  (current : InvoiceHeader.Raw)
  (key : ControlKey)
  (argument : Input)
  : Except ModelForm.Rejection InvoiceHeader.Raw := do
  let decoded := ModelView.decodeKey InvoiceHeader.form {} current key (some argument) Env.nil
  let invocation ← (decoded.run' supply).mapError .ofAction
  return invocation.value

private def control (value : InvoiceHeader.Raw) (label : String) : IO Display.Control := do
  let some control := (ModelView.render InvoiceHeader.form value {} [] Env.nil).controls.find?
      (·.label == label)
    | throw (IO.userError s!"FAIL missing control {label}")
  return control

private def evidence (control : Display.Control) : Display.Evidence :=
  match control.input with
  | .field _ evidence => evidence
  | .choice .. => .unsupported
  | .lookup .. => .unsupported
  | .action => .unsupported
  | .tabs .. => .unsupported

private def isStale : Display.Evidence → Bool
  | .linked _ stale => stale
  | .missing => false
  | .unsupported => false

def run : IO Unit := do
  let initial := InvoiceHeader.initial
  let number ← control initial "Invoice number"
  let issued ← control initial "Issued on"
  let total ← control initial "Total"
  let note ← control initial "Internal note"
  check "EvidenceStatesOfInitialInvoice"
    (evidence number == .linked { page := 1, cellIds := [4], text := "INV-2026-0042" } false &&
      evidence issued == .missing && isStale (evidence total) && evidence note == .unsupported)
  let date : Evidence := { page := 1, cellIds := [6], text := "2026-11-03" }
  let picked ← IO.ofExcept ((perform initial issued.key (.pick date)).mapError toString)
  check "EvidencePickWritesValueAndCells"
    (toJson picked == toJson { initial with
      issued := some (.ofYearMonthDayClip 2026 11 3)
      issuedEvidence := some date })
  check "EvidencePickIsNotStale" (evidence (← control picked "Issued on") == .linked date false)
  let edited ← IO.ofExcept ((perform picked issued.key (.text "2026-11-04")).mapError toString)
  check "EvidenceEditKeepsCellsAndMarksStale"
    (edited.issuedEvidence == some date &&
      evidence (← control edited "Issued on") == .linked date true)
  let reformatted ← IO.ofExcept ((perform initial total.key (.text "1234.5")).mapError toString)
  check "EvidenceStaleComparesParsedValues" (!isStale (evidence (← control reformatted "Total")))
  let paid ← control initial "Paid"
  let stamp : Evidence := { page := 1, cellIds := [21], text := "PAID" }
  let stamped ← IO.ofExcept ((perform initial paid.key (.pick stamp)).mapError toString)
  check "EvidencePickReadsCheckbox"
    (stamped.paid && stamped.paidEvidence == some stamp &&
      evidence (← control stamped "Paid") == .linked stamp false)
  let unticked ← IO.ofExcept ((perform stamped paid.key (.boolean false)).mapError toString)
  check "EvidenceCheckboxEditMarksStale" (isStale (evidence (← control unticked "Paid")))
  let customer : Evidence := { page := 1, cellIds := [8], text := "Example Retail AG" }
  check "EvidenceUnreadablePickIsRejected"
    (match perform initial total.key (.pick customer) with
    | .error (.input message) => message.startsWith "Could not read \"Example Retail AG\""
    | .error (.stale _)
    | .error (.clientBug _)
    | .error (.idCollision _)
    | .ok _ => false)
  check "EvidencePickOnPlainFieldIsClientBug"
    (match perform initial note.key (.pick customer) with
    | .error rejection => rejection == .clientBug .noEvidence
    | .ok _ => false)
  let pickJson := Json.mkObj [("pick", toJson date)]
  check "EvidencePickProtocolDecodes"
    (match InputProtocol.fromJson pickJson with
    | .ok (.pick decoded) => decoded == date
    | .ok (.text _)
    | .ok (.boolean _)
    | .ok (.texts _)
    | .ok (.search _)
    | .ok (.choose _)
    | .error _ => false)

end Tests.Evidence
