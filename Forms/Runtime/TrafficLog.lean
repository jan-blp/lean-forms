import Lean.Data.Json
import Mathlib.Data.FinEnum

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
  deriving DecidableEq

instance : FinEnum Style :=
  FinEnum.ofList [.request, .success, .rejection, .failure, .detail, .key, .string, .number, .literal]
    (by intro style; cases style <;> simp)

inductive AnsiCode where
  | reset
  | bold
  | dim
  | red
  | green
  | yellow
  | blue
  | magenta
  | cyan

private def AnsiCode.toNat : AnsiCode → Nat
  | .reset => 0
  | .bold => 1
  | .dim => 2
  | .red => 31
  | .green => 32
  | .yellow => 33
  | .blue => 34
  | .magenta => 35
  | .cyan => 36

private def Style.toTag (style : Style) : Nat :=
  (FinEnum.equiv style).val

private def Style.ofTag (tag : Nat) : Option Style :=
  if h : tag < FinEnum.card Style then
    some (FinEnum.equiv.symm ⟨tag, h⟩)
  else none

def Style.tag (style : Style) (document : Format) : Format :=
  .tag style.toTag document

private def Style.codes : Style → List AnsiCode
  | .request => [.bold, .cyan]
  | .success => [.bold, .green]
  | .rejection => [.bold, .yellow]
  | .failure => [.bold, .red]
  | .detail => [.dim]
  | .key => [.blue]
  | .string => [.green]
  | .number => [.magenta]
  | .literal => [.yellow]

private def AnsiCode.escape (code : AnsiCode) : String := s!"\x1b[{code.toNat}m"

private def Style.escape (style : Style) : String :=
  String.join (style.codes.map AnsiCode.escape)

private def escapeStyle : Option Style → String
  | none => ""
  | some style => style.escape

private structure RenderState where
  output : String := ""
  column : Nat := 0
  styles : List (Option Style) := []

private instance : Format.MonadPrettyFormat (StateM RenderState) where
  pushOutput text := modify fun state =>
    { state with output := state.output ++ text, column := state.column + text.length }
  pushNewline indent := modify fun state =>
    { state with output := state.output ++ "\n" ++ String.ofList (List.replicate indent ' '), column := indent }
  currColumn := return (← get).column
  startTag tag := modify fun state =>
    let style := Style.ofTag tag
    { state with output := state.output ++ escapeStyle style, styles := style :: state.styles }
  endTags count := do
    if count > 0 then
      modify fun state =>
        let styles := state.styles.drop count
        let restore := String.join (styles.reverse.map escapeStyle)
        { state with output := state.output ++ AnsiCode.reset.escape ++ restore, styles }

def render (document : Format) (color : Bool) (width : Nat := 80) : String :=
  if color then
    let action : StateM RenderState Unit := document.prettyM width
    (action.run {}).2.output
  else document.pretty width

private def heading (style : Style) (text : String) : Format :=
  style.tag (.text text)

private partial def jsonDocument : Lean.Json → Format
  | .null => Style.literal.tag (.text "null")
  | .bool value => Style.literal.tag (Lean.Json.bool value).render
  | .num value => Style.number.tag (Lean.Json.num value).render
  | .str value => Style.string.tag (Lean.Json.str value).render
  | .arr values =>
      Format.bracket "[" (Format.joinSep (values.map jsonDocument).toList ("," ++ Format.line)) "]"
  | .obj fields =>
      let entries := fields.foldl (fun entries key value =>
        let entry := Format.group (
          Style.key.tag (Lean.Json.str key).render ++ ":" ++ Format.line ++ jsonDocument value)
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
    title ++ Style.detail.tag (.text s!" ({contentType}, {body.toUTF8.size} bytes)") ++ .line

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
