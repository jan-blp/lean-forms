module

public import Std.Http
public import Forms.Runtime.TrafficLog
public import Forms.ExampleForms.FormFingerprint

@[expose] public section

namespace Forms.Runtime.Web
open Std Http Async

structure ComponentEndpoint where
  submit : Lean.Json → Except Lean.Json Unit

inductive GetRoute where
  | index
  | script
  | wasmLoader
  | wasmBinary
  | stylesheet
  | compiledSpecification
  deriving DecidableEq, Lean.ToJson

/-- Also generated into `web/generated/routes.ts`. -/
def GetRoute.path : GetRoute → String
  | .index => "/"
  | .script => "/app.js"
  | .wasmLoader => "/wasm/forms.mjs"
  | .wasmBinary => "/wasm/forms.wasm"
  | .stylesheet => "/style.css"
  | .compiledSpecification => "/api/compiled-form"

def GetRoute.all : List GetRoute :=
  [.index, .script, .wasmLoader, .wasmBinary, .stylesheet, .compiledSpecification]

theorem GetRoute.mem_all (route : GetRoute) : route ∈ all := by
  cases route <;> decide

def GetRoute.ofPath (path : String) : Option GetRoute :=
  all.find? (·.path == path)

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
  | wasm (content : ByteArray)

def ResponseBody.contentType : ResponseBody → Option String
  | .empty => none
  | .html _ => some "text/html; charset=utf-8"
  | .javascript _ => some "text/javascript; charset=utf-8"
  | .css _ => some "text/css; charset=utf-8"
  | .json _ => some "application/json"
  | .text _ => some "text/plain; charset=utf-8"
  | .wasm _ => some "application/wasm"

def ResponseBody.bytes : ResponseBody → ByteArray
  | .empty => .empty
  | .html content | .javascript content | .css content | .text content => content.toUTF8
  | .json content => content.compress.toUTF8
  | .wasm content => content

def requestErrorJson (message : String) : Lean.Json :=
  Lean.Json.mkObj [("error", Lean.Json.mkObj [
    ("kind", Lean.toJson "request"), ("message", Lean.toJson message)])]

def respond
  (logger : TrafficLog.Logger)
  (request : String)
  (status : Status)
  (body : ResponseBody)
  : Async (Response Body.Full) := do
  let contentType := body.contentType
  let bytes := body.bytes
  logger.write (TrafficLog.response request status.toCode.toNat (contentType.getD "") bytes)
  let response := Response.new.status status |>.header! "Cache-Control" "no-store"
  -- Lean's upstream Emscripten runtime uses shared WebAssembly memory.
  let response := response.header! "Cross-Origin-Opener-Policy" "same-origin"
    |>.header! "Cross-Origin-Embedder-Policy" "require-corp"
  let response := match contentType with
    | none => response
    | some contentType => response.header! "Content-Type" contentType
  response.fromBytes bytes

structure Application where
  logger : TrafficLog.Logger
  form : ComponentEndpoint
  html : String
  script : String
  wasmLoader : Option String
  wasmBinary : Option ByteArray
  style : String
  compiledForm : Lean.Json

def Application.get
  (app : Application)
  (route : GetRoute)
  : Option ResponseBody :=
  match route with
  | .index => some (.html app.html)
  | .script => some (.javascript app.script)
  | .wasmLoader => app.wasmLoader.map .javascript
  | .wasmBinary => app.wasmBinary.map .wasm
  | .stylesheet => some (.css app.style)
  | .compiledSpecification => some (.json app.compiledForm)

def Application.submit
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

instance : Server.Handler Application where
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
        match app.get route with
        | some body => respond .ok body
        | none => respond .notFound (.text "WebAssembly assets are not built. Run make -f wasm/makefile, restart forms-web, then reload.")
    | .submit => app.submit label request

def openDefaultBrowser (url : String) : IO Unit := do
  let command := if System.Platform.isOSX then "open" else "xdg-open"
  try
    let result ← IO.Process.output { cmd := command, args := #[url], stdin := .null }
    if result.exitCode != 0 then
      IO.eprintln s!"Could not open browser ({command} exited with {result.exitCode}). Open {url} manually."
  catch error =>
    IO.eprintln s!"Could not open browser: {error}. Open {url} manually."

/-- Whether `needle` occurs in `haystack`. -/
def containsBytes (haystack needle : ByteArray) : Bool := Id.run do
  if needle.size > haystack.size then return false
  for i in [0:haystack.size - needle.size + 1] do
    let mut j := 0
    while j < needle.size && haystack[i + j]! == needle[j]! do j := j + 1
    if j == needle.size then return true
  return false

/-- The fingerprint is a string literal in the Wasm data segment. -/
def checkWasmFingerprint (binary : ByteArray) : IO Unit :=
  unless containsBytes binary ExampleForms.formFingerprint.toUTF8 do
    throw (IO.userError
      "web/dist/wasm/forms.wasm is stale (fingerprint mismatch). Run make -f wasm/makefile, then restart forms-web.")

def run
  (name : String)
  (form : RegisteredForm)
  (port : UInt16 := 8080)
  (openBrowser : Bool := false)
  : IO Unit := do
  let wasmBinary ← if ← System.FilePath.pathExists "web/dist/wasm/forms.wasm"
    then some <$> IO.FS.readBinFile "web/dist/wasm/forms.wasm" else pure none
  if let some binary := wasmBinary then checkWasmFingerprint binary
  let app : Application := {
    compiledForm := Lean.toJson (form.descriptor name ExampleForms.formFingerprint)
    logger := ← TrafficLog.Logger.create
    form := { submit := form.definition.verify name ExampleForms.formFingerprint }
    html := ← IO.FS.readFile "web/index.html"
    script := ← IO.FS.readFile "web/dist/app.js"
    wasmLoader := ← if ← System.FilePath.pathExists "web/dist/wasm/forms.mjs"
      then some <$> IO.FS.readFile "web/dist/wasm/forms.mjs" else pure none
    wasmBinary
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
