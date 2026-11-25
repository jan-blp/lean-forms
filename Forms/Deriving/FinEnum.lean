module

public import Mathlib.Data.FinEnum
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Command

public section
namespace Forms.Deriving.FinEnum

/-- A list without duplicates whose elements all have `index` at least `start`. -/
structure Ordered
  {α : Type _}
  (index : α → Nat)
  (start : Nat)
  (list : List α)
  : Prop where
  nodup : list.Nodup
  bounded : ∀ x ∈ list, start ≤ index x

theorem Ordered.nil
  {α : Type _}
  {index : α → Nat}
  {start : Nat}
  : Ordered index start [] where
  nodup := List.nodup_nil
  bounded := fun _ member => nomatch member

/-- Prepends a block of values that all have index `start`. -/
theorem Ordered.append
  {α : Type _}
  {index : α → Nat}
  {start : Nat}
  {block rest : List α}
  (nodup : block.Nodup)
  (indexed : ∀ x ∈ block, index x = start)
  (ordered : Ordered index (start + 1) rest)
  : Ordered index start (block ++ rest) where
  nodup := List.nodup_append.mpr ⟨nodup, ordered.nodup, fun x inBlock y inRest same => by
    have := ordered.bounded y inRest
    rw [← same, indexed x inBlock] at this
    omega⟩
  bounded := fun x member => by
    rcases List.mem_append.mp member with inBlock | inRest
    · exact Nat.le_of_eq (indexed x inBlock).symm
    · exact Nat.le_of_succ_le (ordered.bounded x inRest)

end Forms.Deriving.FinEnum
end

public meta section
namespace Forms.Deriving.FinEnum
open Lean Elab Command

/-- The terms enumerating a constructor's values. -/
private structure Block where
  values : Term
  nodup : Term
  member : Term
  indexed : Term

/-- The tuples of field values, as a list, its `Nodup` proof, the tuple pattern binding `names`,
and a proof that this tuple is in the list. -/
private structure Tuples where
  list : Term
  nodup : Term
  pattern : Term
  member : Term

private def tuples
  (ctor : Ident)
  (fields : List Term)
  (names : List Ident)
  : CommandElabM Tuples := do
  match fields, names with
  | [field], [name] =>
    return {
      list := ← `(FinEnum.toList $field)
      nodup := ← `(FinEnum.nodup_toList)
      pattern := name
      member := ← `(FinEnum.mem_toList $name) }
  | field :: fields, name :: names =>
    let rest ← tuples ctor fields names
    return {
      list := ← `(FinEnum.toList $field ×ˢ $(rest.list))
      nodup := ← `(List.Nodup.product FinEnum.nodup_toList $(rest.nodup))
      pattern := ← `(($name, $(rest.pattern)))
      member := ← `(List.mem_product.mpr ⟨FinEnum.mem_toList $name, $(rest.member)⟩) }
  | _, _ => throwError "FinEnum deriving: mismatched fields of {ctor}"

private def block
  (ctor : Ident)
  (fields : List Term)
  (names : List Ident)
  (applied : Term)
  : CommandElabM Block := do
  if fields.isEmpty then
    return {
      values := ← `([$applied])
      nodup := ← `(List.nodup_singleton _)
      member := ← `(List.mem_singleton_self _)
      indexed := ← `(List.forall_mem_singleton.mpr rfl) }
  let primed := names.map fun name => mkIdent (name.getId.appendAfter "'")
  let tuple ← tuples ctor fields names
  let other ← tuples ctor fields primed
  return {
    values := ← `($(tuple.list).map fun $(tuple.pattern) => $applied)
    nodup := ← `(List.Nodup.map
      (fun $(tuple.pattern) $(other.pattern) same => by cases same; rfl)
      $(tuple.nodup))
    member := ← `(List.mem_map.mpr ⟨$(tuple.pattern), $(tuple.member), rfl⟩)
    indexed := ← `(List.forall_mem_map.mpr fun $(tuple.pattern) _ => rfl) }

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
    let result ← block (mkCIdent ctorName) fields.toList names applied
    let pattern ← `($(mkCIdent ctorName) $(names.toArray):ident*)
    return (result, pattern)
  -- The list is `L₀ ++ (L₁ ++ (… ++ []))`, so constructor `i` sits under `i` right steps.
  let all ← ctors.foldrM (init := ← `([])) fun (result, _) rest => `($(result.values) ++ $rest)
  let ordered ← ctors.foldrM (init := ← `(Ordered.nil)) fun (result, _) rest =>
    `(Ordered.append $(result.nodup) $(result.indexed) $rest)
  let arms ← ctors.mapIdxM fun index (result, pattern) => do
    let mut proof ← `(List.mem_append.mpr (.inl $(result.member)))
    for _ in [0:index] do
      proof ← `(List.mem_append.mpr (.inr $proof))
    `(Parser.Term.matchAltExpr| | $pattern => $proof)
  let type := mkCIdent name
  elabCommand <| ← `(command|
    instance : FinEnum $type :=
      FinEnum.ofNodupList $all
        (fun x => match x with $arms:matchAlt*)
        (Ordered.nodup (index := $(mkCIdent (name ++ `ctorIdx))) (start := 0) $ordered))

initialize registerDerivingHandler ``FinEnum fun names => do
  for name in names do
    derive name
  return true

end Forms.Deriving.FinEnum
