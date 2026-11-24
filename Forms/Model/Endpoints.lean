module

public import Forms.Model.Remote
public meta import Forms.Deriving.FinEnum

@[expose] public section
namespace Forms.Model
open Lean

syntax endpointCase := ppLine atomic((docComment)? "| ") ident " : " term " at " str

private meta structure EndpointCase where
  ref : Syntax
  doc : Option (TSyntax ``Parser.Command.docComment)
  ctor : Ident
  input : Term
  output : Term
  path : StrLit

macro doc:(docComment)? "endpoints " name:ident " where" cases:endpointCase* : command => do
  let parsed : Array EndpointCase ← cases.mapM fun
    | case@`(endpointCase| $[$caseDoc]? | $ctor:ident : $type at $path) => do
      let (input, output) ← match (⟨Parser.Term.dropParens type⟩ : Term) with
        | `($input → $output) => pure (input, output)
        | _ => pure (← `(Unit), type)
      if let `($_ → $_) := (⟨Parser.Term.dropParens output⟩ : Term) then
        Macro.throwErrorAt output "endpoints take one input; use a structure"
      pure {
        ref := case
        doc := caseDoc
        ctor
        input
        output
        path }
    | _ => Macro.throwUnsupported
  let mut seen : List String := []
  for endpoint in parsed do
    if seen.contains endpoint.path.getString then
      Macro.throwErrorAt endpoint.path s!"duplicate path {endpoint.path.getString}"
    seen := endpoint.path.getString :: seen
  let qualified (ctor : Ident) := mkIdent (name.getId ++ ctor.getId)
  let ctors ← parsed.mapM fun endpoint =>
    `(Parser.Command.ctor| $[$endpoint.doc:docComment]? | $endpoint.ctor:ident)
  let signatures ← parsed.mapM fun endpoint => withRef endpoint.ref
    `(Parser.Term.matchAltExpr|
      | $(qualified endpoint.ctor):ident =>
        { Input := $endpoint.input, Output := $endpoint.output })
  let paths ← parsed.mapM fun endpoint =>
    `(Parser.Term.matchAltExpr| | $(qualified endpoint.ctor):ident => $endpoint.path)
  let signature := mkIdent (name.getId ++ `signature)
  let type ← `($[$doc:docComment]? inductive $name where
    $ctors:ctor*
    deriving DecidableEq, FinEnum, Repr)
  -- Elaborate supplied types outside the namespace, so constructors cannot shadow them.
  let implementation ← `(@[expose] def endpointSignature : $name → Api.Signature :=
    fun $signatures:matchAlt*)
  let definition ← `(@[expose] def $signature : $name → Api.Signature := endpointSignature)
  let api ← `(instance : Api $name where
    signature := $signature
    path := fun $paths:matchAlt*
    distinct := by decide)
  `($type:command
    $implementation:command
    $definition:command
    $api:command)

end Forms.Model
