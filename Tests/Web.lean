module

public import Forms.Runtime.Web
public import Forms.ExampleForms.Counter
public import Forms.ExampleForms.Person
public import Forms.ExampleForms.Invoice
public import Forms.ExampleForms.Shapes

@[expose] public section

namespace Tests.Web
open Forms Forms.Runtime Forms.Composition Forms.ExampleForms

def check (name : String) (passed : Bool) : IO Unit := do
  unless passed do throw (IO.userError s!"FAIL {name}")

def errorsJson {ty : DataType}
  (refined : RefinedDataType ty)
  (draft : String)
  : IO Lean.Json := do
  let value ← IO.ofExcept (JsonProtocol.valueFromJson ty (← IO.ofExcept (Lean.Json.parse draft)))
  return Lean.toJson ((RefinedDataType.errors refined value).map Validation.ResolvedError.toJson)

def located {ty : DataType}
  (message : String)
  (locations : List (Validation.Location ty))
  (nonempty : locations ≠ [] := by simp)
  : Lean.Json :=
  Validation.ResolvedError.toJson { message := message, targets := .fields locations nonempty }

def testPreciseErrors : IO Unit := do
  let positive := "Quantity and unit price must be at least 1."
  let both ← errorsJson Invoice.invoiceType
    "[{\"description\":\"A\",\"quantity\":\"0\",\"unitPrice\":\"0\"},{\"description\":\"B\",\"quantity\":\"0\",\"unitPrice\":\"5\"}]"
  check "ListErrorsPerItemAndField" (both == Lean.toJson [located (ty := Invoice.invoice) positive [.item 0 (.field .quantity .self)],
    located (ty := Invoice.invoice) positive [.item 0 (.field .unitPrice .self)], located (ty := Invoice.invoice) positive [.item 1 (.field .quantity .self)]])
  let shapes ← errorsJson Shapes.shapeType "{\"tag\":\"rectangle\",\"value\":{\"width\":\"0\",\"height\":\"2\"}}"
  check "SumErrorNamesTagAndPayloadField" (shapes == Lean.toJson [located (ty := Shapes.shape) "Size must be at least 1." [.constructor .rectangle (.field .width .self)]])
  let circle ← errorsJson Shapes.shapeType "{\"tag\":\"circle\",\"value\":\"0\"}"
  check "SumErrorNamesScalarPayload" (circle == Lean.toJson [located (ty := Shapes.shape) "Size must be at least 1." [.constructor .circle .self]])

def run : IO Unit := do
  testPreciseErrors
  let refined : RefinedDataType .natural := .refine (.base .natural)
    (.ofChecker <| .when (.not (.natLe (.project .self) (.value 5)))
      (.report (.value "At most five") (.global)))
  let form := Runtime.Web.ComponentEndpoint.ofComponent refined Counter.form 0
  let history ← IO.ofExcept (ComponentHistory.replay Counter.form 0 #[⟨.plusFive, ()⟩])
  discard <| IO.ofExcept (form.submit (ComponentHistoryProtocol.encode history))
  let invalid ← IO.ofExcept (history.apply ⟨.plusOne, ()⟩)
  check "WebChecksRefinementsAfterReplay" (match form.submit (ComponentHistoryProtocol.encode invalid) with
    | .error error => error == (SubmissionProtocol.Error.invalidValue (ty := .natural) [⟨"At most five", .global⟩]).toJson
    | .ok _ => false)
  let unlocated := SubmissionProtocol.Error.invalidValue (ty := .natural) [⟨"Rule", .global⟩]
  let root := SubmissionProtocol.Error.invalidValue (ty := .natural) [⟨"Rule", .fields [.self]⟩]
  check "ValidationDistinguishesRootAndNoTarget" (unlocated.toJson != root.toJson)
  check "ValidationSerializesNoTarget"
    ((unlocated.toJson.getObjValAs? (List Lean.Json) "errors").toOption ==
      some [Lean.Json.mkObj [("message", Lean.toJson "Rule"), ("targets", Validation.TargetResolution.toJson (root := .natural) .global)]])
  let targets : Validation.TargetResolution Person.person :=
    .fields [.field .name .self, .field .age .self]
  let error : Validation.ResolvedError Person.person := { message := "Both fields", targets := targets }
  check "ValidationLiftsEveryTarget"
    ((error.mapLocations (.item 2)).targets.toJson ==
      (Validation.TargetResolution.fields [
        .item 2 (.field .name .self), .item 2 (.field .age .self)]
        (root := .list Person.person)).toJson)
  let forged : ComponentHistory Counter.form := { history with value := 4 }
  check "WebRejectsForgedFinalValue" (match form.submit (ComponentHistoryProtocol.encode forged) with
    | .error error => error == (SubmissionProtocol.Error.invocation (ty := .natural) .valueMismatch).toJson
    | .ok _ => false)
  check "WebDoesNotChangeInitialStateAfterSubmission" (match form.submit (ComponentHistoryProtocol.encode history) with
    | .ok () => true
    | .error _ => false)
  IO.println "PASS: web replay verification, refinements, and trusted initial state"

end Tests.Web
