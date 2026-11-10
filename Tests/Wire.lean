module

public import Forms.Runtime.Wire
import Forms.Protocol.TypeScriptAst
meta import Forms.Protocol.TypeScript

public section
namespace Tests.Wire
open Lean Forms.Protocol Forms.Runtime.Wire

structure OptionalSample where
  required : Option String
  omitted? : Option String
  deriving ToJson, FromJson

private def check (message : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError message)

private def roundtrip {α : Type} [ToJson α] [FromJson α] (value : α) : IO Unit := do
  let encoded := toJson value
  let decoded : α ← IO.ofExcept (fromJson? encoded)
  check "Wire roundtrip changed the JSON" (toJson decoded == encoded)

def run : IO Unit := do
  let absent : OptionalSample := { required := none, omitted? := none }
  roundtrip absent
  roundtrip ({ required := some "a", omitted? := some "b" } : OptionalSample)
  check "Nullable field must be present" (((toJson absent).getObjVal? "required").toOption == some Json.null)
  check "Optional field must be omitted" (!((toJson absent).getObjVal? "omitted").isOk)
  for event in [Event.apply "key" Json.null, .apply "key" (toJson "12"),
      .submit, .reset, .complete 200 "ok", .failed "offline"] do
    roundtrip event
    roundtrip (Command.event event)
  check "Payload-free constructors encode as strings" (toJson Event.submit == toJson "submit")
  check "Payload constructors encode under their name" ((toJson (Event.apply "key" (toJson "12"))).getObjValD "apply" ==
    Json.mkObj [("key", toJson "key"), ("argument", toJson "12")])
  check "Missing apply argument accepted" (!(fromJson? (Json.mkObj [
    ("apply", Json.mkObj [("key", toJson "key")])]) : Except String Event).isOk)
  check "Generated schema omitted dependencies" ((typescript% [Forms.Runtime.Wire.Command]).modules.any
    (·.declarations.any (·.name == "Event")))
  let schema := typescript% [OptionalSample]
  check "Optional structure field was not optional in TS" (schema.modules.any (·.pretty.contains "\"omitted\"?: string"))
  check "Generated optional fields have wrong AST" (schema.modules == [⟨["Tests", "Wire"], [
    ⟨"OptionalSample", .object [
      .mk "required" (.union .string .null []), .mk "omitted" .string true]⟩]⟩])
  let wire := (typescript% [Forms.Runtime.Wire.Snapshot]).modules
  check "Types were not grouped by namespace" (wire.map (·.file) ==
    ["Forms/Runtime/Wire.ts", "FormsReact.ts"])
  check "Cross-namespace reference was not imported" (wire.any fun m => m.file == "Forms/Runtime/Wire.ts" &&
    m.pretty.contains "import type * as FormsReact from \"../../FormsReact.js\";" &&
    m.pretty.contains "\"view\": FormsReact.Component")
  check "Relative import paths changed" (TS.relativeImport ["A", "B", "C"] ["A", "D", "E"] == "../D/E.js" &&
    TS.relativeImport ["A", "B"] ["A", "B", "C"] == "./B/C.js" && TS.relativeImport ["A", "B", "C"] ["A", "B"] == "../B.js")
  let nested : TS.Type := .array (.union (.reference [] "Node") .null [])
  check "Array union precedence changed" (nested.pretty == "(Node | null)[]")
  check "Nested array printing changed" ((TS.Type.array nested).pretty == "(Node | null)[][]")
  check "Tuple printing changed" ((TS.Type.tuple [.string, nested]).pretty ==
    "[string, (Node | null)[]]")
  check "String literal escaping changed" ((TS.Type.stringLiteral "a\"\n").pretty ==
    "\"a\\\"\\n\"")
  IO.println "PASS built-in JSON codecs and generated TypeScript"

end Tests.Wire
