module

public import Forms.Protocol.TypeScriptAst
public meta import Forms.Protocol.TypeScriptAst

public meta import Lean.Elab.Term
public meta import Lean.Meta

public meta section
namespace Forms.Protocol
open Lean Meta Elab TS

private def fieldName (name : Name) : String := name.eraseMacroScopes.getString!

/-- The Lean namespace of `name`, which selects its TypeScript module. -/
private def modulePath (name : Name) : MetaM (List String) := do
  if name.getPrefix.isAnonymous then throwError "TypeScript types need a namespace: {name}"
  return name.getPrefix.components.map Name.getString!

private partial def tsType (type : Expr) : MetaM TS.Type := do
  let fn := type.getAppFn.constName!
  let args := type.getAppArgs
  if fn == ``String then return .string
  if fn == ``Bool then return .boolean
  if fn == ``Nat || fn == ``Int then return .number
  if fn == ``Json then return .unknown
  if fn == ``Option then return .union (← tsType args[0]!) .null []
  if fn == ``List || fn == ``Array then return .array (← tsType args[0]!)
  if fn == ``Prod then return .tuple [← tsType args[0]!, ← tsType args[1]!]
  unless args.isEmpty do throwError "Unsupported wire type: {type}"
  let info ← getConstInfoInduct fn
  unless info.numIndices == 0 && info.numParams == 0 do
    throwError "Indexed types belong behind the wire boundary: {type}"
  return .reference (← modulePath fn) fn.getString!

private def tsField (name : String) (type : Expr) (isStruct : Bool) : MetaM Property := do
  if isStruct && name.endsWith "?" then
    unless type.isAppOf ``Option do throwError "Optional JSON field must have type Option: {name}"
    let key := name.dropEndWhile (· == '?') |>.toString
    return .mk key (← tsType type.getAppArgs[0]!) true
  return .mk name (← tsType type)

private def declaration (name : Name) : MetaM TypeAlias := do
  let info ← getConstInfoInduct name
  unless info.numParams == 0 && info.numIndices == 0 do throwError "Wire types must be unindexed and monomorphic"
  let isStruct := isStructure (← getEnv) name
  if isStruct && !(getStructureParentInfo (← getEnv) name).isEmpty then
    throwError "Wire structures must declare their fields directly"
  let variants ← info.ctors.mapM fun ctorName => do
    let ctor ← getConstInfoCtor ctorName
    forallTelescopeReducing ctor.type fun fields _ => do
      let decls ← fields.mapM fun field => field.fvarId!.getDecl
      let parts ← decls.mapM fun decl => tsField (fieldName decl.userName) decl.type isStruct
      let object := TS.Type.object parts.toList
      if isStruct then return object
      if fields.isEmpty then return .stringLiteral ctor.name.getString!
      let payload ← if decls.all (! ·.userName.hasMacroScopes) then pure object
        else if fields.size == 1 then tsType decls[0]!.type
        else do
          let types ← decls.mapM fun decl => tsType decl.type
          pure (.tuple types.toList)
      return .object [.mk ctor.name.getString! payload]
  let type ← match variants with
    | [] => throwError "Empty wire types are unsupported: {name}"
    | [type] => pure type
    | first :: second :: rest => pure (.union first second rest)
  return ⟨name.getString!, type⟩

private partial def collectTypes (type : Expr) (seen : Array Name) : MetaM (Array Name) := do
  let fn := type.getAppFn.constName!
  if [``String, ``Bool, ``Nat, ``Int, ``Json].contains fn then return seen
  if [``Option, ``List, ``Array, ``Prod].contains fn then
    type.getAppArgs.foldlM (fun seen arg => collectTypes arg seen) seen
  else
    if seen.contains fn then return seen
    let info ← getConstInfoInduct fn
    unless info.numParams == 0 && info.numIndices == 0 do throwError "Unsupported wire type: {type}"
    let mut seen := seen.push fn
    for ctor in info.ctors do
      let ctor ← getConstInfoCtor ctor
      seen ← forallTelescopeReducing ctor.type fun fields _ =>
        fields.foldlM (fun seen field => do collectTypes (← inferType field) seen) seen
    return seen

elab "typescript%" "[" names:ident,* "]" : term => do
  let mut types := #[]
  for name in names.getElems do
    types ← collectTypes (← Term.elabType name) types
  let mut modules : Array TS.Module := #[]
  for name in types do
    let path ← modulePath name
    let decl ← declaration name
    modules := match modules.findIdx? (·.path == path) with
      | some i => modules.modify i fun m => { m with declarations := m.declarations ++ [decl] }
      | none => modules.push ⟨path, [decl]⟩
  for module in modules do
    let mut taken := module.declarations.map (·.name)
    for path in module.imports do
      if taken.contains (alias path) then
        throwError "TypeScript import alias {alias path} clashes in {module.file}"
      taken := alias path :: taken
  return toExpr (Program.mk modules.toList)

end Forms.Protocol
