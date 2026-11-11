module

public import Mathlib.Data.FinEnum
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Command

public meta section
namespace Forms.Deriving.FinEnum
open Lean Elab Command

/-- `FinEnum` instance listing the constructors in declaration order; requires `DecidableEq`. -/
def derive (name : Name) : CommandElabM Unit := do
  let info ← liftCoreM <| getConstInfoInduct name
  unless info.numParams == 0 && info.numIndices == 0 do
    throwError "FinEnum deriving requires a type without parameters or indices"
  let ctors ← info.ctors.toArray.mapM fun ctorName => do
    let ctor ← liftCoreM <| getConstInfoCtor ctorName
    unless ctor.numFields == 0 do
      throwError "FinEnum deriving requires nullary constructors, but {ctorName} has fields"
    return mkCIdent ctorName
  elabCommand <| ← `(command|
    instance : FinEnum $(mkCIdent name) :=
      FinEnum.ofNodupList [$ctors,*]
        (fun x => by cases x <;> simp)
        (by decide))

initialize registerDerivingHandler ``FinEnum fun names => do
  for name in names do
    derive name
  return true

end Forms.Deriving.FinEnum
