import Std.Http
import Forms.Runtime.TrafficLog
import Forms.Runtime.CompositionProtocol
import Forms.Runtime.SubmissionProtocol

namespace Forms.Runtime.Web
open Std Http Async

structure ComponentEndpoint where
  specification : Lean.Json
  submit : Lean.Json → Except Lean.Json Unit

def ComponentEndpoint.ofComponent {ty : DataType}
  (refined : RefinedDataType ty)
  (component : Composition.Component ty)
  (initial : ⟦ty⟧)
  : ComponentEndpoint where
  specification := CompositionProtocol.specificationToJson refined component initial
  submit submission := do
    discard <| (SubmissionProtocol.verify refined component initial submission).mapError (·.toJson)

inductive GetRoute where
  | index
  | script
  | interpreter
  | validation
  | stylesheet
  | specification

def GetRoute.ofPath (path : String) : Option GetRoute :=
  if path == "/" then some .index
  else if path == "/app.js" then some .script
  else if path == "/interpreter.js" then some .interpreter
  else if path == "/validation.js" then some .validation
  else if path == "/style.css" then some .stylesheet
  else if path == "/api/form" then some .specification
  else none

inductive Route where
  | get (route : GetRoute)
  | submit

def Route.ofPath (path : String) : Option Route :=
  if path == "/api/submit" then some .submit
  else (GetRoute.ofPath path).map .get

def Route.method : Route → Method
  | .get _ => .get
  | .submit => .post

inductive ResponseBody where
  | empty
  | html (content : String)
  | javascript (content : String)
  | css (content : String)
  | json (content : Lean.Json)
  | text (content : String)

private def ResponseBody.contentType : ResponseBody → Option String
  | .empty => none
  | .html _ => some "text/html; charset=utf-8"
  | .javascript _ => some "text/javascript; charset=utf-8"
  | .css _ => some "text/css; charset=utf-8"
  | .json _ => some "application/json"
  | .text _ => some "text/plain; charset=utf-8"

private def ResponseBody.serialize : ResponseBody → String
  | .empty => ""
  | .html content => content
  | .javascript content => content
  | .css content => content
  | .json content => content.compress
  | .text content => content

private def requestErrorJson (message : String) : Lean.Json :=
  Lean.Json.mkObj [("error", Lean.Json.mkObj [
    ("kind", Lean.toJson "request"), ("message", Lean.toJson message)])]

private def respond
  (logger : TrafficLog.Logger)
  (request : String)
  (status : Status)
  (body : ResponseBody)
  : Async (Response Body.Full) := do
  let contentType := body.contentType
  let body := body.serialize
  logger.write (TrafficLog.response request status.toCode.toNat (contentType.getD "") body)
  let response := Response.new.status status |>.header! "Cache-Control" "no-store"
  let response := match contentType with
    | none => response
    | some contentType => response.header! "Content-Type" contentType
  response.fromBytes body.toUTF8

private structure Application where
  logger : TrafficLog.Logger
  form : ComponentEndpoint
  html : String
  script : String
  interpreter : String
  validation : String
  style : String

private def Application.get
  (app : Application)
  (route : GetRoute)
  : ResponseBody :=
  match route with
  | .index => .html app.html
  | .script => .javascript app.script
  | .interpreter => .javascript app.interpreter
  | .validation => .javascript app.validation
  | .stylesheet => .css app.style
  | .specification => .json app.form.specification

private def Application.submit
  (app : Application)
  (label : String)
  (request : Request Body.Stream)
  : Async (Response Body.Full) := do
  let respond := respond app.logger label
  let body ← try request.body.readAll (maximumSize := some (1024 * 1024))
    catch _ =>
      app.logger.write (TrafficLog.request label (some (.text "Body could not be read within the 1 MiB limit")))
      return ← respond .payloadTooLarge
        (.json (requestErrorJson "Request body could not be read within the 1 MiB limit"))
  app.logger.write (TrafficLog.request label (some (TrafficLog.json body)))
  match Lean.Json.parse body with
  | .error error => respond .badRequest (.json (requestErrorJson error))
  | .ok submission =>
      match app.form.submit submission with
      | .error error => respond .unprocessableEntity (.json (Lean.Json.mkObj [("error", error)]))
      | .ok () => respond .noContent .empty

private instance : Server.Handler Application where
  ResponseBody := Body.Full
  onRequest app request := do
    let label := s!"{request.line.method} {request.line.uri}"
    let respond := respond app.logger label
    let some route := Route.ofPath (toString request.line.uri.path)
      | app.logger.write (TrafficLog.request label)
        respond .notFound (.text "Not found")
    if request.line.method != route.method then
      app.logger.write (TrafficLog.request label)
      let response ← respond .methodNotAllowed (.text "Method not allowed")
      return { response with line.headers :=
        response.line.headers.insert (.mk "allow") (.ofString! (toString route.method)) }
    match route with
    | .get route =>
        app.logger.write (TrafficLog.request label)
        respond .ok (app.get route)
    | .submit => app.submit label request

private def openDefaultBrowser (url : String) : IO Unit := do
  let command := if System.Platform.isOSX then "open" else "xdg-open"
  try
    let result ← IO.Process.output { cmd := command, args := #[url], stdin := .null }
    if result.exitCode != 0 then
      IO.eprintln s!"Could not open browser ({command} exited with {result.exitCode}). Open {url} manually."
  catch error =>
    IO.eprintln s!"Could not open browser: {error}. Open {url} manually."

def run {ty : DataType}
  (refined : RefinedDataType ty)
  (component : Composition.Component ty)
  (initial : ⟦ty⟧)
  (port : UInt16 := 8080)
  (openBrowser : Bool := false)
  : IO Unit := do
  let app : Application := {
    logger := ← TrafficLog.Logger.create
    form := .ofComponent refined component initial
    html := ← IO.FS.readFile "web/index.html"
    script := ← IO.FS.readFile "web/dist/app.js"
    interpreter := ← IO.FS.readFile "web/dist/interpreter.js"
    validation := ← IO.FS.readFile "web/dist/validation.js"
    style := ← IO.FS.readFile "web/style.css"
  }
  Async.block do
    let address : Net.SocketAddress := .v4 ⟨.ofParts 127 0 0 1, port⟩
    let server ← Server.serve address app
    let url := s!"http://127.0.0.1:{port}"
    IO.println s!"Open {url}"
    (← IO.getStdout).flush
    if openBrowser then discard <| IO.asTask (openDefaultBrowser url) (prio := .dedicated)
    server.waitShutdown

end Forms.Runtime.Web
