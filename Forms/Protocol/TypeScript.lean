module

public meta import Lean.Elab.Term
public meta import Lean.Meta

public meta section
namespace Forms.Protocol
open Lean Meta Elab

private def fieldName (name : Name) : String := name.eraseMacroScopes.getString!
private def quoted (text : String) : String := (Json.str text).compress

private partial def tsType (type : Expr) : MetaM String := do
  let fn := type.getAppFn.constName!
  let args := type.getAppArgs
  if fn == ``String then return "string"
  if fn == ``Bool then return "boolean"
  if fn == ``Nat || fn == ``Int then return "number"
  if fn == ``Json then return "unknown"
  if fn == ``Option then return s!"({← tsType args[0]!} | null)"
  if fn == ``List || fn == ``Array then return s!"({← tsType args[0]!})[]"
  if fn == ``Prod then return s!"[{← tsType args[0]!}, {← tsType args[1]!}]"
  unless args.isEmpty do throwError "Unsupported wire type: {type}"
  let info ← getConstInfoInduct fn
  unless info.numIndices == 0 && info.numParams == 0 do
    throwError "Indexed types belong behind the wire boundary: {type}"
  return fn.getString!

private def tsField (name : String) (type : Expr) (isStruct : Bool) : MetaM String := do
  if isStruct && name.endsWith "?" then
    unless type.isAppOf ``Option do throwError "Optional JSON field must have type Option: {name}"
    let key := name.dropEndWhile (· == '?') |>.toString
    return s!"{quoted key}?: {← tsType type.getAppArgs[0]!}"
  return s!"{quoted name}: {← tsType type}"

private def declaration (name : Name) : MetaM String := do
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
      let object := "{ " ++ String.intercalate "; " parts.toList ++ " }"
      if isStruct then return object
      if fields.isEmpty then return quoted ctor.name.getString!
      let payload ← if decls.all (! ·.userName.hasMacroScopes) then pure object
        else if fields.size == 1 then tsType decls[0]!.type
        else do
          let types ← decls.mapM fun decl => tsType decl.type
          pure ("[" ++ String.intercalate ", " types.toList ++ "]")
      return "{ " ++ quoted ctor.name.getString! ++ ": " ++ payload ++ " }"
  return "export type " ++ name.getString! ++ " = " ++ String.intercalate " | " variants ++ ";\n"

private partial def collectTypes (type : Expr) (seen : Array Name) : MetaM (Array Name) := do
  let fn := type.getAppFn.constName!
  if [``String, ``Bool, ``Nat, ``Int, ``Json].contains fn then return seen
  if [``Option, ``List, ``Array, ``Prod].contains fn then
    type.getAppArgs.foldlM (fun seen arg => collectTypes arg seen) seen
  else
    if seen.contains fn then return seen
    if seen.any (fun name => name.getString! == fn.getString!) then
      throwError "Duplicate TypeScript type name: {fn.getString!}"
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
  let declarations ← types.toList.mapM fun name => declaration name
  return mkStrLit (String.join declarations)

end Forms.Protocol
