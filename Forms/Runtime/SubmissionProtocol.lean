import Forms.Runtime.ComponentHistoryProtocol

namespace Forms.Runtime.SubmissionProtocol
open Lean Composition

inductive Error (ty : DataType) where
  | invocation (error : ComponentHistoryProtocol.Error)
  | invalidValue (errors : List (Validation.ResolvedError ty))

instance {ty : DataType} : ToString (Error ty) where
  toString
    | .invocation error => toString error
    | .invalidValue [] => "Invalid form value"
    | .invalidValue (error :: errors) =>
        String.intercalate "\n" ((error :: errors).map fun error =>
          match error.targets with
          | .global => error.message
          | .fields _ _ => error.message
          | .invalidTarget _ => "Invalid validation target: " ++ error.message).eraseDups

def Error.toJson {ty : DataType} (error : Error ty) : Json :=
  let details := match error with
    | .invocation _ => [("kind", Lean.toJson "replay")]
    | .invalidValue errors =>
        [("kind", Lean.toJson "validation"), ("errors", Lean.toJson (errors.map fun error =>
          Json.mkObj [("message", Lean.toJson error.message), ("targets", error.targets.toJson)]))]
  Json.mkObj (("message", Lean.toJson (toString error)) :: details)

def verify {ty : DataType}
  (refined : RefinedDataType ty)
  (component : Component ty)
  (initial : ⟦ty⟧)
  (submission : Json)
  : Except (Error ty) (ComponentHistory component) := do
  let history ← (ComponentHistoryProtocol.verify component initial submission).mapError Error.invocation
  let some _ := RefinedDataType.validate refined history.value
    | throw (.invalidValue (RefinedDataType.errors refined history.value))
  return history

end Forms.Runtime.SubmissionProtocol
