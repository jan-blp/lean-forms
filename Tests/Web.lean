import Forms.Runtime.Web
import Forms.ExampleForms.Counter

namespace Tests.Web
open Forms Forms.Runtime Forms.Composition Forms.ExampleForms

private def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

private def testTrafficLog : IO Unit := do
  let body := TrafficLog.json "{\"value\":\"12345678901234567890\",\"actions\":[]}"
  let document := TrafficLog.request "POST /api/submit" (some body)
  let plain := TrafficLog.render document false 35
  let colored := TrafficLog.render document true 35
  check "TrafficPlainHasNoAnsi" (!(plain.contains "\x1b"))
  check "TrafficRequestIsCyan" (colored.contains "\x1b[36m")
  let stripped := ([0, 1, 32, 33, 34, 35, 36] : List Nat).foldl
    (fun text code => text.replace s!"\x1b[{code}m" "") colored
  check "TrafficColorsPreserveLayout" (stripped == plain)
  for (status, code) in [(200, "32"), (422, "33"), (500, "31")] do
    let message := TrafficLog.render (TrafficLog.response "POST /api/submit" status "application/json" "{}") true
    check "TrafficStatusColor" (message.contains s!"\x1b[{code}m")
    check "TrafficHeadingStyleEndsBeforePayload" (message.contains "\x1b[0m\n  {}")
  check "TrafficNoContentHasNoPayload"
    (TrafficLog.render (TrafficLog.response "POST /api/submit" 204 "" "") false ==
      "SERVER → CLIENT 204 POST /api/submit\n")
  let sample := "{\"key\":[\"text\",42,true,false,null,{},[]]}"
  let value ← IO.ofExcept (Lean.Json.parse sample)
  let highlighted := TrafficLog.render (TrafficLog.json sample) true 20
  check "TrafficJsonKeysBlue" (highlighted.contains "\x1b[34m\"key\"\x1b[0m")
  check "TrafficJsonStringsGreen" (highlighted.contains "\x1b[32m\"text\"\x1b[0m")
  check "TrafficJsonNumbersMagenta" (highlighted.contains "\x1b[35m42\x1b[0m")
  for literal in ["true", "false", "null"] do
    check "TrafficJsonLiteralsYellow" (highlighted.contains s!"\x1b[33m{literal}\x1b[0m")
  check "TrafficJsonKeepsLeanLayout" (TrafficLog.render (TrafficLog.json sample) false 20 == value.pretty 20)
  let nested := TrafficLog.Style.success.tag
    (.text "outer " ++ TrafficLog.Style.key.tag (.text "inner") ++ .text " outer")
  check "TrafficRestoresOuterStyle" ((TrafficLog.render nested true).contains "inner\x1b[0m\x1b[1m\x1b[32m outer")

def run : IO Unit := do
  testTrafficLog
  let refined : RefinedDataType .natural := .refine (.base .natural)
    { condition := .natLe (.project .self) (.value 5), errorMessage := "At most five" }
  let form := Runtime.Web.ComponentEndpoint.ofComponent refined Counter.form 0
  let history ← IO.ofExcept (ComponentHistory.replay Counter.form 0 #[⟨.plusFive, ()⟩])
  discard <| IO.ofExcept (form.submit (ComponentHistoryProtocol.encode history))
  let invalid ← IO.ofExcept (history.apply ⟨.plusOne, ()⟩)
  check "WebChecksRefinementsAfterReplay" (match form.submit (ComponentHistoryProtocol.encode invalid) with
    | .error error => error == .invalidValue ["At most five"]
    | .ok _ => false)
  check "WebExplainsFailedRefinement"
    (toString (Web.Error.invalidValue ["At most five"]) == "At most five")
  check "WebReportsDistinctFailures"
    (toString (Web.Error.invalidValue ["First rule", "Second rule", "First rule"]) == "First rule\nSecond rule")
  let forged : ComponentHistory Counter.form := { history with value := 4 }
  check "WebRejectsForgedFinalValue" (match form.submit (ComponentHistoryProtocol.encode forged) with
    | .error error => error == .invocation .valueMismatch
    | .ok _ => false)
  check "WebDoesNotChangeInitialStateAfterSubmission" (match form.submit (ComponentHistoryProtocol.encode history) with
    | .ok () => true
    | .error _ => false)
  IO.println "PASS: web replay verification, refinements, and trusted initial state"

end Tests.Web
