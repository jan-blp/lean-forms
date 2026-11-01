import Std.Http
import Forms.Runtime.TrafficLog
import Forms.Runtime.CompositionProtocol
import Forms.Runtime.ComponentHistoryProtocol

namespace Forms.Runtime.Web
open Std Http Async

inductive Error where
  | invocation (error : ComponentHistoryProtocol.Error)
  | invalidValue
  deriving BEq

instance : ToString Error where
  toString
    | .invocation error => toString error
    | .invalidValue => "Invalid replayed value"

structure Form where
  specification : String
  submit : Lean.Json → Except Error Unit

def Form.ofComponent {ty : DataType}
  (refined : RefinedDataType ty)
  (component : Composition.Component ty)
  (initial : ⟦ty⟧)
  : Form where
  specification := CompositionProtocol.encode refined component initial
  submit submission := do
    let history ← (ComponentHistoryProtocol.verify component initial submission).mapError Error.invocation
    let some _ := RefinedDataType.validate refined history.value
      | throw .invalidValue
    return ()

private def errorJson (message : String) : String :=
  (Lean.Json.mkObj [("error", Lean.toJson message)]).compress

private def respond
  (logger : TrafficLog.Logger)
  (request : String)
  (status : Status)
  (contentType : String)
  (body : String)
  : Async (Response Body.Full) := do
  logger.write (TrafficLog.response request status.toCode.toNat contentType body)
  let response := Response.new.status status |>.header! "Cache-Control" "no-store"
  let response := if contentType.isEmpty then response else response.header! "Content-Type" contentType
  response.fromBytes body.toUTF8

private structure Application where
  logger : TrafficLog.Logger
  form : Form
  html : String
  script : String
  interpreter : String
  style : String

private instance : Server.Handler Application where
  ResponseBody := Body.Full
  onRequest app request := do
    let respond := respond app.logger
    let path := toString request.line.uri.path
    let label := s!"{request.line.method} {request.line.uri}"
    let submissionRequest := request.line.method == .post && path == "/api/submit"
    unless submissionRequest do app.logger.write (TrafficLog.request label)
    if request.line.method == .get then
      if path == "/" then respond label .ok "text/html; charset=utf-8" app.html
      else if path == "/app.js" then respond label .ok "text/javascript; charset=utf-8" app.script
      else if path == "/interpreter.js" then respond label .ok "text/javascript; charset=utf-8" app.interpreter
      else if path == "/style.css" then respond label .ok "text/css; charset=utf-8" app.style
      else if path == "/api/form" then respond label .ok "application/json" app.form.specification
      else respond label .notFound "text/plain; charset=utf-8" "Not found"
    else if submissionRequest then
      let body ← try request.body.readAll (maximumSize := some (1024 * 1024))
        catch _ =>
          app.logger.write (TrafficLog.request label (some (.text "Body could not be read within the 1 MiB limit")))
          return ← respond label .payloadTooLarge "application/json"
            (errorJson "Request body could not be read within the 1 MiB limit")
      app.logger.write (TrafficLog.request label (some (TrafficLog.json body)))
      match Lean.Json.parse body with
      | .error error => respond label .badRequest "application/json" (errorJson error)
      | .ok submission =>
          match app.form.submit submission with
          | .error error => respond label .unprocessableEntity "application/json" (errorJson (toString error))
          | .ok () => respond label .noContent "" ""
    else
      let response ← respond label .methodNotAllowed "text/plain; charset=utf-8" "Method not allowed"
      return { response with line.headers := response.line.headers.insert (.mk "allow") (.ofString! "GET, POST") }

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
