module

public import Forms.Runtime.Wire
import Forms.Runtime.DisplayProtocol
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
      .draft "key" "12", .submit, .reset, .complete 200 "ok", .failed "offline"] do
    roundtrip event
    roundtrip (Command.event event)
  check "Payload-free constructors encode as strings" (toJson Event.submit == toJson "submit")
  check "Payload constructors encode under their name" ((toJson (Event.draft "key" "12")).getObjValD "draft" ==
    Json.mkObj [("key", toJson "key"), ("argument", toJson "12")])
  check "Missing draft argument accepted" (!(fromJson? (Json.mkObj [
    ("draft", Json.mkObj [("key", toJson "key")])]) : Except String Event).isOk)
  -- Intentionally bypass browser validation: Lean accepts " 8" and owns input errors.
  let editor := Forms.Runtime.DisplayLayout.control {} {
    key := ⟨"age"⟩, target := {}, label := "Age", disabled := false,
    location := [], input := .natural 8 }
  let noValidate := match editor.toWire with
    | some (.element .form attrs _ _ _ _ _ _) => attrs.contains ("novalidate", "")
    | _ => false
  check "Editor forms must leave validation to Lean" noValidate
  let child := Node.element .input [] [] [] none (some "hello") none (some "key")
  roundtrip (Node.element .div [("class", "form")] [none, some child]
    [⟨.input, .draft, "key", "input", .value⟩] (some "title") none none none)
  check "Generated schema omitted dependencies" ((typescript% [Forms.Runtime.Wire.Command]).declarations.any (·.name == "Event"))
  check "Optional structure field was not optional in TS" ((typescript% [OptionalSample]).pretty.contains "\"omitted\"?: string")
  let schema := typescript% [OptionalSample]
  check "Generated optional fields have wrong AST" (schema.declarations == [
    ⟨"OptionalSample", .object [
      .mk "required" (.union .string .null []), .mk "omitted" .string true]⟩])
  let nested : TS.Type := .array (.union (.reference "Node") .null [])
  check "Array union precedence changed" (nested.pretty == "(Node | null)[]")
  check "Nested array printing changed" ((TS.Type.array nested).pretty == "(Node | null)[][]")
  check "Tuple printing changed" ((TS.Type.tuple [.string, nested]).pretty ==
    "[string, (Node | null)[]]")
  check "String literal escaping changed" ((TS.Type.stringLiteral "a\"\n").pretty ==
    "\"a\\\"\\n\"")
  IO.println "PASS built-in JSON codecs and generated TypeScript"

end Tests.Wire
