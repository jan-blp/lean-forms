module

public import Mathlib.Data.FinEnum
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Command

public meta section
namespace Forms.Deriving.FinEnum
open Lean Elab Command

/-- A constructor's values, one per combination of its fields' values, and a proof that the
value with fields `names` is among them. -/
private def ctorValues
  (ctor : Ident)
  (fields : List Term)
  (names : List Ident)
  (applied : Term)
  : CommandElabM (Term × Term) := do
  match fields, names with
  | [], [] => return (← `([$applied]), ← `(List.mem_singleton_self _))
  | [field], [name] =>
    return (← `((FinEnum.toList $field).map fun $name => $applied),
      ← `(List.mem_map.mpr ⟨$name, FinEnum.mem_toList $name, rfl⟩))
  | field :: fields, name :: names =>
    let (inner, member) ← ctorValues ctor fields names applied
    return (← `((FinEnum.toList $field).flatMap fun $name => $inner),
      ← `(List.mem_flatMap.mpr ⟨$name, FinEnum.mem_toList $name, $member⟩))
  | _, _ => throwError "FinEnum deriving: mismatched fields of {ctor}"

/-- `FinEnum` instance listing the constructors in declaration order; a constructor with fields
is listed once per combination of their values. Requires `DecidableEq`. -/
def derive (name : Name) : CommandElabM Unit := do
  let info ← liftCoreM <| getConstInfoInduct name
  unless info.numParams == 0 && info.numIndices == 0 do
    throwError "FinEnum deriving requires a type without parameters or indices"
  let ctors ← info.ctors.toArray.mapM fun ctorName => do
    let ctor ← liftCoreM <| getConstInfoCtor ctorName
    let mut type := ctor.type
    let mut fields : Array Term := #[]
    for _ in [0:ctor.numFields] do
      let .forallE _ field body _ := type
        | throwError "FinEnum deriving could not read the fields of {ctorName}"
      if field.hasLooseBVars then
        throwError "FinEnum deriving requires the fields of {ctorName} not to be dependent"
      fields := fields.push (← liftTermElabM <| PrettyPrinter.delab field)
      type := body
    let names := (List.range fields.size).map fun index => mkIdent (.mkSimple s!"field{index}")
    let args : Array Term := names.toArray.map fun name => ⟨name.raw⟩
    let applied ← `($(mkCIdent ctorName) $args*)
    let (values, member) ← ctorValues (mkCIdent ctorName) fields.toList names applied
    let pattern ← `($(mkCIdent ctorName) $(names.toArray):ident*)
    return (values, member, pattern)
  -- The list is `L₀ ++ (L₁ ++ (… ++ []))`, so constructor `i` sits under `i` right steps.
  let all ← ctors.foldrM (init := ← `([])) fun (values, _, _) rest => `($values ++ $rest)
  let arms ← ctors.mapIdxM fun index (_, member, pattern) => do
    let mut proof ← `(List.mem_append.mpr (.inl $member))
    for _ in [0:index] do
      proof ← `(List.mem_append.mpr (.inr $proof))
    `(Parser.Term.matchAltExpr| | $pattern => $proof)
  elabCommand <| ← `(command|
    instance : FinEnum $(mkCIdent name) :=
      FinEnum.ofNodupList $all
        (fun x => match x with $arms:matchAlt*)
        (by decide +kernel))

initialize registerDerivingHandler ``FinEnum fun names => do
  for name in names do
    derive name
  return true

end Forms.Deriving.FinEnum
