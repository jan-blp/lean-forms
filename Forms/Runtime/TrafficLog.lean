import Lean.Data.Json

namespace Forms.Runtime.TrafficLog
open Std

inductive Style where
  | request
  | success
  | rejection
  | failure
  | detail
  | key
  | string
  | number
  | literal

private def Style.code : Style → Nat
  | .request => 36
  | .success => 32
  | .rejection => 33
  | .failure => 31
  | .detail => 2
  | .key => 34
  | .string => 32
  | .number => 35
  | .literal => 33

private def escape (code : Nat) : String := s!"\x1b[{code}m"

private structure RenderState where
  output : String := ""
  column : Nat := 0
  styles : List Nat := []

private instance : Format.MonadPrettyFormat (StateM RenderState) where
  pushOutput text := modify fun state =>
    { state with output := state.output ++ text, column := state.column + text.length }
  pushNewline indent := modify fun state =>
    { state with output := state.output ++ "\n" ++ String.ofList (List.replicate indent ' '), column := indent }
  currColumn := return (← get).column
  startTag code := modify fun state =>
    { state with output := state.output ++ escape code, styles := code :: state.styles }
  endTags count := do
    if count > 0 then
      modify fun state =>
        let styles := state.styles.drop count
        let restore := String.join (styles.reverse.map escape)
        { state with output := state.output ++ escape 0 ++ restore, styles }

def render (document : Format) (color : Bool) (width : Nat := 80) : String :=
  if color then
    let action : StateM RenderState Unit := document.prettyM width
    (action.run {}).2.output
  else document.pretty width

private def heading (style : Style) (text : String) : Format :=
  .tag 1 (.tag style.code (.text text))

private partial def jsonDocument : Lean.Json → Format
  | .null => .tag Style.literal.code (.text "null")
  | .bool value => .tag Style.literal.code (Lean.Json.bool value).render
  | .num value => .tag Style.number.code (Lean.Json.num value).render
  | .str value => .tag Style.string.code (Lean.Json.str value).render
  | .arr values =>
      Format.bracket "[" (Format.joinSep (values.map jsonDocument).toList ("," ++ Format.line)) "]"
  | .obj fields =>
      let entries := fields.foldl (fun entries key value =>
        let entry := Format.group (
          .tag Style.key.code (Lean.Json.str key).render ++ ":" ++ Format.line ++ jsonDocument value)
        entry :: entries) []
      Format.bracket "{" (Format.joinSep entries ("," ++ Format.line)) "}"

def json (body : String) : Format :=
  match Lean.Json.parse body with
  | .ok value => jsonDocument value
  | .error _ => jsonDocument (Lean.toJson body)

def request (label : String) (body : Option Format := none) : Format :=
  let title := heading .request s!"CLIENT → SERVER {label}"
  match body with
  | none => title ++ .line
  | some body => title ++ .nest 2 (.line ++ body) ++ .line

def response
  (label : String)
  (status : Nat)
  (contentType : String)
  (body : String)
  : Format :=
  let style := if status ≥ 500 then Style.failure else if status ≥ 400 then .rejection else .success
  let title := heading style s!"SERVER → CLIENT {status} {label}"
  if status == 204 then title ++ .line
  else if contentType == "application/json" then
    title ++ .nest 2 (.line ++ json body) ++ .line
  else
    title ++ .tag Style.detail.code (.text s!" ({contentType}, {body.toUTF8.size} bytes)") ++ .line

structure Logger where
  output : IO.FS.Stream
  color : Bool

def Logger.create : IO Logger := do
  let output ← IO.getStdout
  let noColor ← IO.getEnv "NO_COLOR"
  let term ← IO.getEnv "TERM"
  return { output, color := (← output.isTty) && noColor.isNone && term != some "dumb" }

def Logger.write (logger : Logger) (document : Format) : IO Unit := do
  logger.output.putStrLn (render document logger.color)
  logger.output.flush

end Forms.Runtime.TrafficLog
