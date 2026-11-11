module

public import Forms.Model.Remote
public meta import Forms.Deriving.FinEnum

@[expose] public section
namespace Forms.Model
open Lean

syntax endpointCase := ppLine (docComment)? "| " ident " : " term " at " str

/-- Declares endpoints, one per `| name : Input → Output at "/path"`; `| name : Output` takes `Unit`.
Generates the inductive and its `Api` instance. -/
macro doc:(docComment)? "endpoints " name:ident " where" cases:endpointCase* : command => do
  let parsed ← cases.mapM fun case => match case with
    | `(endpointCase| $[$caseDoc]? | $ctor:ident : $type at $path) => do
      let (input, output) ← match (⟨Parser.Term.dropParens type⟩ : Term) with
        | `($input → $output) => pure (input, output)
        | _ => pure (← `(Unit), type)
      if let `($_ → $_) := (⟨Parser.Term.dropParens output⟩ : Term) then
        Macro.throwErrorAt output "endpoints take one input; use a structure"
      pure (case, caseDoc, ctor, input, output, path)
    | _ => Macro.throwUnsupported
  let mut seen : List String := []
  for (_, _, _, _, _, path) in parsed do
    if seen.contains path.getString then
      Macro.throwErrorAt path s!"duplicate path {path.getString}"
    seen := path.getString :: seen
  let qualified (ctor : Ident) := mkIdent (name.getId ++ ctor.getId)
  let ctors ← parsed.mapM fun (_, caseDoc, ctor, _) =>
    `(Lean.Parser.Command.ctor| $[$caseDoc:docComment]? | $ctor:ident)
  let signatures ← parsed.mapM fun (case, _, ctor, input, output, _) => withRef case
    `(Lean.Parser.Term.matchAltExpr|
      | $(qualified ctor):ident => { Input := $input, Output := $output })
  let paths ← parsed.mapM fun (_, _, ctor, _, _, path) =>
    `(Lean.Parser.Term.matchAltExpr| | $(qualified ctor):ident => $path)
  let signature := mkIdent (name.getId ++ `signature)
  let type ← `($[$doc:docComment]? inductive $name where
    $ctors:ctor*
    deriving DecidableEq, FinEnum, Repr)
  -- Elaborate the supplied types in the caller's namespace, where endpoint
  -- constructors cannot shadow them through the signature declaration's name.
  let implementation ← `(@[expose] def endpointSignature : $name → Api.Signature := fun named =>
    match named with $signatures:matchAlt*)
  let definition ← `(@[expose] def $signature : $name → Api.Signature := endpointSignature)
  let api ← `(instance : Api $name where
    signature := $signature
    path := fun named => match named with $paths:matchAlt*
    distinct := by decide)
  `($type:command
    $implementation:command
    $definition:command
    $api:command)

end Forms.Model
