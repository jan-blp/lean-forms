module

public import Forms.Runtime.ModelForm
public import Forms.Runtime.InputProtocol
public import Forms.Runtime.DisplayProtocol
public import Forms.Runtime.ReactView
public import Forms.Runtime.Wire

@[expose] public section
namespace Forms.Runtime
open Lean

structure Submission (α : Type) where
  form : String
  fingerprint : String
  value : α
  deriving ToJson, FromJson

/-- The body of a successful submit response: the document the server stored. -/
structure Saved (α : Type) where
  value : α
  deriving ToJson, FromJson

def ModelForm.SubmitOutcome.ofSuccess
  {α : Type}
  [FromJson α]
  (body : String)
  : ModelForm.SubmitOutcome α :=
  match Json.parse body >>= fromJson? (α := Saved α) with
  | .ok saved => .accepted saved.value
  | .error message => .unreachable s!"Could not read the saved form: {message}"

def ModelForm.SubmitOutcome.ofFailure
  {α : Type}
  (status : Nat)
  (body : String)
  : ModelForm.SubmitOutcome α :=
  match FeedbackProtocol.serverError? body with
  | some error => .rejected error
  | none => .unreachable s!"Submission failed (HTTP {status})."

def httpEffect (request : Model.HttpRequest) : Wire.HttpEffect :=
  { url := request.url
    method := match request.method with
      | .get => .GET
      | .post => .POST
    headers := { «Content-Type» := "application/json" }
    body := request.body }

def fetchEffect (fetch : Model.HttpFetch) : Wire.Effect :=
  .fetch (toJson fetch).compress (httpEffect fetch.request)

def fetchOfId (id : String) : Except String Model.HttpFetch :=
  Json.parse id >>= fromJson?

def callOfId (id : String) : Except String Model.Uuid :=
  if canonical : Model.Uuid.isCanonical id then .ok ⟨id, canonical⟩ else .error "Invalid call id"

def responseJson : Wire.HttpOutcome → Except String Json
  | .response status body => if 200 ≤ status && status < 300 then Json.parse body
    else .error s!"The server responded with status {status}."
  | .unreachable message => .error message

def ModelForm.Snapshot.toWire
  {α : Type}
  [ToJson α]
  (snapshot : ModelForm.Snapshot α)
  (formName fingerprint submitUrl : String)
  : Wire.Snapshot :=
  let submission := toJson ({ form := formName, fingerprint, value := snapshot.value } : Submission α)
  let view := snapshot.view.toReactPage snapshot.ui (toJson snapshot.value).pretty
  { title := snapshot.view.title
    view
    draftFields := view.draftFields
    pickFields := view.pickFields
    hostWidgets := view.hostWidgets.eraseDups
    rejection := snapshot.ui.rejection
    controls := snapshot.controls.map DisplayProtocol.controlToJson
    submission
    errors := snapshot.errors.map FeedbackProtocol.errorToJson
    effects := snapshot.effects.map fun
      | .submit => .submit {
          url := submitUrl
          method := .POST
          headers := { «Content-Type» := "application/json" }
          body := some submission.compress }
      | .fetch request => fetchEffect request
      | .call call => .call call.id.value (httpEffect call.request)
      | .focus key => .focus (ControlKeyProtocol.toString key) }

def ModelForm.Event.fromWire
  {α : Type}
  [FromJson α]
  : Wire.Event → Except String (ModelForm.Event α)
  | .apply key argument => do
    let argument ← InputProtocol.argumentFromJson (if argument == .null then none else some argument)
    pure (.apply (← ControlKeyProtocol.fromString key) argument)
  | .submit => .ok .submit
  | .draft key message => do
    pure (.draft (← ControlKeyProtocol.fromString key) message)
  | .reset => .ok .reset
  | .submitted (.response status body) =>
    .ok (.submitted (if 200 ≤ status && status < 300 then .ofSuccess body
      else .ofFailure status body))
  | .submitted (.unreachable message) => .ok (.submitted (.unreachable message))
  | .fetched id outcome => do
    pure (.loaded (← fetchOfId id) (responseJson outcome))
  | .called id outcome => do
    pure (.called (← callOfId id) (responseJson outcome))

end Forms.Runtime
